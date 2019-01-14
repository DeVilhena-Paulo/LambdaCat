open PPrint
open Source

(** [type_error pos msg] reports a type error and exits. *)
let type_error pos msg =
  Printf.eprintf "%s:\n%s\n"
    (Position.string_of_pos pos)
    msg;
  exit 1

(** [string_of_type ty] returns a human readable representation of a type. *)
let string_of_type t =
  let rec ty = function
    | TyConstant TyFloat ->
       string "float"
    | TyArrow (input, output) ->
       group (mayparen_ty_under_arrow_lhs input) ^^ break 1
       ^^ string "->"
       ^^ break 1 ^^ (group (ty output))
    | TyPair (lhs, rhs) ->
       group (mayparen_ty_under_pair_lhs lhs) ^^ break 1
       ^^ string "* " ^^ group (mayparen_ty_under_pair_rhs rhs)
    and mayparen_ty_under_arrow_lhs = function
      | (TyArrow _) as t ->
         PPrintCombinators.parens (ty t)
      | t ->
         ty t
    and mayparen_ty_under_pair_lhs = function
      | (TyArrow _) as t ->
         PPrintCombinators.parens (ty t)
      | t ->
         ty t
    and mayparen_ty_under_pair_rhs = function
      | (TyArrow _ | TyPair _) as t ->
         PPrintCombinators.parens (ty t)
      | t ->
         ty t
  in
  let b = Buffer.create 13 in
  PPrintEngine.ToBuffer.pretty 0.8 80 b (group (ty t));
  Buffer.contents b

exception UnboundValue of term' Position.located
exception InconsistentTypes of typ * typ * term' Position.located
exception OnlyFunctionsCanBeApplied of term' Position.located
exception OnlyPairsCanBeDestructed of term' Position.located

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

(** [check_program source] returns [source] if it is well-typed or
   reports an error if it is not. *)
let check_program (source : program_with_locations) : program_with_locations =
  let (ty_env : (identifier, typ) Hashtbl.t) = Hashtbl.create 13 in

  let type_primitive : primitive -> typ =
    let ty = TyConstant TyFloat in function
    | Sin | Cos | Exp | Inv | Neg -> TyArrow (ty, ty)
    | Add | Mul -> TyArrow (ty, (TyArrow (ty, ty)))
  in

  let rec check_term ({ value; position } as t : term' Position.located) : typ =
    match value with
    | Var x ->
       begin try Hashtbl.find ty_env x with _ -> raise (UnboundValue t) end
    | App (t, u) ->
       let ty_u = check_term u in
       let ty_t = check_term t in
       begin match ty_t with
       | TyArrow (ty_t1, ty_t2) when ty_t1 = ty_u -> ty_t2
       | TyArrow (_, ty_t2) ->
          raise (InconsistentTypes (ty_t, TyArrow (ty_u, ty_t2), t))
       | _ -> raise (OnlyFunctionsCanBeApplied t)
       end
    | Lam ((x, ty), t) ->
       Hashtbl.add ty_env x ty;
       let ty' = check_term t in
       Hashtbl.remove ty_env x;
       TyArrow (ty, ty')
    | Fst t | Snd t ->
       let ty_t = check_term t in
       begin match ty_t with
       | TyPair (ty, _) when value = Fst t -> ty
       | TyPair (_, ty) when value = Snd t -> ty
       | _ -> raise (OnlyPairsCanBeDestructed t)
       end
    | Pair (t, u) -> TyPair (check_term t, check_term u)
    | Literal l -> TyConstant TyFloat
    | Primitive p -> type_primitive p
  in

  let check_definition (({ Position.value = (x, ty') }, term) as input) =
    type_error_handler
      (fun () ->
       let ty = check_term term in
        begin
          if (ty = ty') then Hashtbl.add ty_env x ty
          else raise (InconsistentTypes (ty, ty', term))
        end;
        input)
  in

  List.map check_definition source


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
