open Source


(* ************************************************************************** *)
(* Error handling                                                             *)
(* ************************************************************************** *)
   
exception UnboundValue of term' Position.located
exception InconsistentTypes of typ * typ * term' Position.located
exception OnlyFunctionsCanBeApplied of term' Position.located
exception OnlyPairsCanBeDestructed of term' Position.located

(** [type_error pos msg] reports a type error and exits. *)
let type_error pos msg =
  Printf.eprintf "%s:\n%s\n"
    (Position.string_of_pos pos)
    msg;
  exit 1

(** [type_error_handler f] returns [f ()] if it doesn't fail and calls [type_error] otherwise. *)
let type_error_handler f =
  try f () with
  | UnboundValue { value; position } ->
     let msg = Printf.sprintf "Unbound value \"%s\"" in
     type_error position (msg (string_of_term' value))
  | InconsistentTypes (ty, ty', { value; position }) ->
     let msg =
       Printf.sprintf "The expression \"%s\" has type \"%s\", but type \"%s\" was expected" in
     type_error position (msg (string_of_term' value) (string_of_type ty) (string_of_type ty'))
  | OnlyFunctionsCanBeApplied { value; position } ->
     let msg = Printf.sprintf "The expression \"%s\" must have an arrow type" in
     type_error position (msg (string_of_term' value))
  | OnlyPairsCanBeDestructed { value; position } ->
     let msg = Printf.sprintf "The expression \"%s\" must have a product type" in
     type_error position (msg (string_of_term' value))


(* ************************************************************************** *)
(* Syntax of typed terms                                                      *)
(* ************************************************************************** *)

type 'a typed = {
    value : 'a;
    type' : typ
  }

type tterm = (tterm typed) Source.t

type program_with_types = (binding * tterm typed) list

let value ({ value; _ } : 'a typed) = value

let type' ({ type'; _ } : 'a typed) = type'

let term_with_type value type' = { value; type' }


(* ************************************************************************** *)
(* Translation from source to typed programs                                  *)
(* ************************************************************************** *)

let type_program (source : program_with_locations) : program_with_types =
  let (ty_env : (identifier, typ) Hashtbl.t) = Hashtbl.create 13 in

  let type_primitive : primitive -> typ =
    let ty = TyConstant TyFloat in function
    | Sin | Cos | Exp | Inv | Neg -> TyArrow (ty, ty)
    | Add | Mul -> TyArrow (ty, (TyArrow (ty, ty)))
  in

  let rec type_term ({ value; position } as t : term' Position.located) : tterm typed =
    match value with
    | Var x as value ->
       begin
         try term_with_type value (Hashtbl.find ty_env x)
         with _ -> raise (UnboundValue t)
       end
    | App (t, u) ->
       let t', u' = type_term t, type_term u in
       begin match type' t' with
       | TyArrow (ty, ty') when ty = type' u' ->
          term_with_type (App (t', u')) ty'
       | TyArrow (_, ty') ->
          raise (InconsistentTypes (type' t', TyArrow (type' u', ty'), t))
       | _ -> raise (OnlyFunctionsCanBeApplied t)
       end
    | Lam ((x, ty), t) ->
       Hashtbl.add ty_env x ty;
       let t' = type_term t in
       Hashtbl.remove ty_env x;
       term_with_type (Lam ((x, ty), t')) (TyArrow (ty, type' t'))
    | Fst t | Snd t ->
       let t' = type_term t in
       let value, type'=
         match type' t' with
         | TyPair (ty, _) when value = Fst t -> (Fst t'), ty
         | TyPair (_, ty) when value = Snd t -> (Snd t'), ty
         | _ -> raise (OnlyPairsCanBeDestructed t) in
       term_with_type value type'
    | Pair (t, u) ->
       let t', u' = type_term t, type_term u in
       term_with_type (Pair (t', u')) (TyPair (type' t', type' u'))
    | Literal l as value ->
       term_with_type value (TyConstant TyFloat)
    | Primitive p as value ->
       term_with_type value (type_primitive p)
  in

  let check_definition ({ Position.value = (x, ty') }, term) =
    type_error_handler
      (fun () ->
       let term' = type_term term in
        begin
          if (type' term' = ty') then Hashtbl.add ty_env x ty'
          else raise (InconsistentTypes (type' term', ty', term))
        end;
        ((x, ty'), term'))
  in

  List.map check_definition source


(* ************************************************************************** *)
(* Checking source program                                                    *)
(* ************************************************************************** *)

(** [check_program source] returns [source] if it is well-typed or
   reports an error if it is not. *)
let check_program (source : program_with_locations) : program_with_locations =
  ignore (type_program source); source

(** [eta_expanse source] makes sure that only functions are defined at
    toplevel and turns them into eta-long forms if needed. *)
let eta_expanse (source : program_with_locations) : program_with_locations =
  let check_definition ((binding, (term : term' Position.located)) as input) =
    match Position.(value term, snd (value binding)) with
    | Lam _, _ -> input
    | _, TyArrow (ty, _) ->
       let open Position in
       let x = Id "Paulo" in
       let var = unknown_pos (Var x) in
       let app = unknown_pos (App (term, var)) in
       let lam = unknown_pos (Lam ((x, ty), app)) in
       (binding, lam)
    | _ -> failwith "Not a function definition" in
  List.map check_definition source

let program : program_with_locations -> program_with_locations = fun source ->
  let xsource = check_program source in
  if !Options.typecheck_only then exit 0;
  eta_expanse xsource
