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

let error_handler = function
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
  | _ -> assert false


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

type 'a or_error = Val of 'a | Exn of exn

module type Monad = sig

  type 'a t

  val return : 'a -> 'a t

  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t

end

module type Context = sig

  type t

  type content

  val make   : unit -> t

  val lookup : t -> identifier -> content option

  val add    : t -> identifier -> content -> t

  val remove : t -> identifier -> t

end

module ContextMonad (C : Context) : sig

  type content = C.content

  include Monad with type 'a t = C.t -> (C.t * 'a or_error)

  val bind_map : 'a list -> ('a -> 'b t) -> ('b list) t

  val raise' : exn -> 'a t

  val lookup : identifier -> (content option) t

  val add    : identifier -> content -> unit t

  val remove : identifier -> unit t

  val run    : 'a t -> catch:(exn -> 'a) -> 'a

end = struct

  type content = C.content

  type 'a t = C.t -> (C.t * 'a or_error)

  let return v = fun context -> (context, Val v)

  let raise' e = fun context -> (context, Exn e)

  let (>>=) m k context =
    let context', a = m context in
    match a with
    | Val a' -> k a' context'
    | Exn e  -> (context, Exn e)

  let rec bind_map xs f =
    match xs with
    | [] -> return []
    | x :: xs ->
       f x           >>= fun x'  ->
       bind_map xs f >>= fun xs' ->
       return (x' :: xs')

  let lookup id = fun context ->
    (context, Val (C.lookup context id))

  let add id ty = fun context ->
    (C.add context id ty, Val ())

  let remove id = fun context ->
    (C.remove context id, Val ())

  let run m ~catch =
    match snd (m (C.make ())) with
    | Val a -> a
    | Exn e -> catch e

end

module HashContext (Content : sig type t end) : sig

  include Context with type content = Content.t

end = struct

  type content = Content.t

  type t = (identifier, content) Hashtbl.t

  let make () = Hashtbl.create 13

  let lookup context id =
    Hashtbl.find_opt context id

  let add context id ty =
    Hashtbl.add context id ty; context

  let remove context id =
    Hashtbl.remove context id; context

end


module TypeChecker (C : Context with type content = typ) = struct

  open Position

  include ContextMonad (C)

  let rec type_term : term' located -> (tterm typed) t = fun t ->
    match value t with
    | Var id            -> type_var id (position t)
    | App (t, u)        -> type_app t u
    | Lam ((id, ty), t) -> type_lam id ty t
    | Fst t             -> type_fst_or_snd true  t
    | Snd t             -> type_fst_or_snd false t
    | Pair (t, u)       -> type_pair t u
    | Literal l         -> type_literal l
    | Primitive p       -> type_primitive p

  and type_var (id : identifier) (pos : position) =
    lookup id >>= function
    | Some typ ->
       return (term_with_type (Var id) typ)
    | None     ->
       raise' (UnboundValue { value = Var id; position = pos})

  and type_app (t : term' located) (u : term' located) =
    type_term t >>= fun t' ->
    type_term u >>= fun u' ->
    match type' t' with
    | TyArrow (ty, ty') when ty = type' u' ->
       return (term_with_type (App (t', u')) ty')
    | TyArrow (_, ty') ->
       raise' (InconsistentTypes (type' t', TyArrow (type' u', ty'), t))
    | _ ->
       raise' (OnlyFunctionsCanBeApplied t)

  and type_lam (id : identifier) (ty : typ) (t : term' located) =
    add id ty   >>= fun _  ->
    type_term t >>= fun t' ->
    remove id   >>= fun _  ->
    return (term_with_type (Lam ((id, ty), t')) (TyArrow (ty, type' t')))

  and type_fst_or_snd (b : bool) (t : term' located) =
    type_term t >>= fun ({ type' } as t') ->
    match type' with
    | TyPair (ty, _) when b ->
       return (term_with_type (Fst t') ty)
    | TyPair (_, ty) ->
       return (term_with_type (Snd t') ty)
    | _ ->
       raise' (OnlyPairsCanBeDestructed t)

  and type_pair (t : term' located) (u : term' located) =
    type_term t >>= fun t' ->
    type_term u >>= fun u' ->
    return (term_with_type (Pair (t', u')) (TyPair (type' t', type' u')))

  and type_literal (l : literal) =
    return (term_with_type (Literal l) (TyConstant TyFloat))

  and type_primitive (p : primitive) =
    let ty = TyConstant TyFloat in
    return (term_with_type (Primitive p)
      (match p with
      | Sin | Cos | Exp | Inv | Neg -> TyArrow (ty, ty)
      | Add | Mul -> TyArrow (ty, (TyArrow (ty, ty)))))


  let type_program : program_with_locations -> program_with_types = fun source ->
    let check_definition ({ Position.value = (id, ty) }, term)  : (_ * tterm typed) t =
      type_term term >>= fun ({ type' } as t') ->
      if type' = ty
      then add id ty >>= fun _ -> return ((id, ty), t')
      else raise' (InconsistentTypes (type', ty, term))
    in
    run (bind_map source check_definition) ~catch:error_handler

end

(* ************************************************************************** *)
(* Checking source program                                                    *)
(* ************************************************************************** *)

(** [check_program source] returns [source] if it is well-typed or
   reports an error if it is not. *)
let check_program (source : program_with_locations) : program_with_locations =
  let module TypeChecker =
    TypeChecker (HashContext (struct type t = typ end)) in
  ignore (TypeChecker.type_program source); source

(** [eta_expantion source] makes sure that only functions are defined at
    toplevel and turns them into eta-long forms if needed. *)
let eta_expantion (source : program_with_locations) : program_with_locations =
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
  eta_expantion xsource
