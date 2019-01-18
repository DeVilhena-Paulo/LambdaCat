open Source
open Typechecker


(* ************************************************************************** *)
(* Auxiliary functions                                                        *)
(* ************************************************************************** *)

let rec traverse (get : 'a -> 'a t) (set : 'a -> 'b t -> 'b) : 'a t -> 'b t = function
  | App (a, b) -> App (traverse' get set a, traverse' get set b)
  | Lam (b, t) -> Lam (b, traverse' get set t)
  | Pair (a, b) -> Pair (traverse' get set a, traverse' get set b)
  | Fst a -> Fst (traverse' get set a)
  | Snd a -> Snd (traverse' get set a)
  | Var x -> Var x
  | Literal l -> Literal l
  | Primitive p -> Primitive p
and traverse' (get : 'a -> 'a t) (set : 'a -> 'b t -> 'b) : 'a -> 'b =
  (fun a -> set a (traverse get set (get a)))

let add_locations =
  traverse (fun a -> a) (fun _ -> Position.unknown_pos)

let remove_locations =
  traverse Position.value (fun _ a -> a)

let i = ref 0

let fresh_var () =
  incr i; Id (Printf.sprintf "'a[%d]" !i)

(** [substitute x u t] substitutes all the free occurences of [x] in [t] by [u],
    that is, "t[x ↦ u]". We avoid capture by assuming that the free variables
    of [u] are all fresh. *)
let substitute (x : identifier) (u : tterm typed) : tterm typed -> tterm typed =
  let set t = function
    | Var y when x = y -> u
    | Lam ((y, _), _) when x = y -> t
    | _ as v -> term_with_type v (type' t) in
  traverse' value set

let type_program_without_locations : program -> program_with_types = fun source ->
  let aux (binding, term) =
    Position.(unknown_pos binding, unknown_pos (add_locations term)) in
  source |> List.map aux |> type_program


(* ************************************************************************** *)
(* Translation from source to 'categorical' programs                          *)
(* ************************************************************************** *)

let rec ok_of_typ : typ -> Target.ok =
  let open Target in function
  | TyArrow (ty, ty') -> OkArrow (ok_of_typ ty, ok_of_typ ty')
  | TyPair  (ty, ty') -> OkPair  (ok_of_typ ty, ok_of_typ ty')
  | TyConstant _      -> OkFloat

let ok_of_term : tterm typed -> Target.ok =
  fun t -> ok_of_typ (type' t)

(** [source_to_categories] translates a [source] in a [target] language
    made of categorical combinators. *)
let source_to_categories : Source.program -> Target.program = fun source ->
  let (env : (identifier, Target.t * Target.ok * Target.ok) Hashtbl.t) = Hashtbl.create 13 in

  let const (_X : Target.ok) (_Y : Target.ok) (t : Target.t) : Target.t =
    App (App (Compose (_X, OkUnit, _Y), App (UnitArrow _Y, t)), It _X)
  in

  let const_fun (_X : Target.ok) (_A : Target.ok) (_B : Target.ok) (f : Target.t) : Target.t =
    App (Curry (_X, _A, _B), App (App (Compose (OkPair (_X, _A), _A, _B), f), Exr (_X, _A)))
  in

  let primitive_to_arrow : primitive -> Target.t * Target.ok * Target.ok =
    let ok = Target.OkFloat in function
    | (Sin | Cos | Exp | Inv | Neg) as p ->
       (Primitive p, ok, ok)
    | (Add | Mul) as p ->
       (App (Curry (ok, ok, ok), Primitive p), ok, OkArrow (ok, ok))
  in

  let rec lam_to_arrow ((x, ty) : binding) : tterm typed -> Target.t = fun t ->
    let open Target in
    let _X, _B = ok_of_typ ty, ok_of_term t in
    match value t with
    | App (u, v) ->
       let _C, _A = ok_of_term u, ok_of_term v in
       let arrow_u = lam_to_arrow (x, ty) u in (* X --\x.u--> A => B *)
       let arrow_v = lam_to_arrow (x, ty) v in (* X --\x.v--> A *)
       let fork = Fork (_X, _C, _A) in
       let apply = Apply (_A, _B) in
       let compose = Compose (_X, OkPair (_C, _A), _B) in
       App (App (compose, apply), App (App (fork, arrow_u), arrow_v))
    | Lam ((y, ty'), u) when x = y ->
       let _C, _Y = ok_of_term u, ok_of_typ ty' in
       const_fun _X _Y _C (lam_to_arrow (y, ty') u)
    | Lam ((y, ty'), u) ->
       let _C, _Y = ok_of_term u, ok_of_typ ty' in
       let z = fresh_var () in
       let var  = term_with_type (Var z) (TyPair (ty, ty')) in
       let fst_ = term_with_type (Fst var) ty  in
       let snd_ = term_with_type (Snd var) ty' in
       u
       |> substitute x fst_
       |> substitute y snd_
       |> lam_to_arrow (z, TyPair (ty, ty'))           (* X x Y --\(x,y).u--> C *)
       |> fun arrow -> App (Curry (_X, _Y, _C), arrow) (* X --\x.\y.u--> Y => C *)
    | Pair (u, v) ->
       let _A, _C = ok_of_term u, ok_of_term v in
       let arrow_u = lam_to_arrow (x, ty) u in (* X --\x.u--> A *)
       let arrow_v = lam_to_arrow (x, ty) v in (* X --\x.v--> C *)
       App (App (Fork (_X, _A, _C), arrow_u), arrow_v)
    | Fst u ->
       let _BxC = ok_of_term u in
       let arrow_u = lam_to_arrow (x, ty) u in (* X --\x.u--> B x C *)
       begin match _BxC with
       | OkPair (_, _C) ->
          App (App (Compose (_X, OkPair (_B, _C), _B), Exl (_B, _C)), arrow_u)
       | _ -> assert false
       end
    | Snd u ->
       let _AxB = ok_of_term u in
       let arrow_u = lam_to_arrow (x, ty) u in (* X --\x.u--> A x B *)
       begin match _AxB with
       | OkPair (_A, _) ->
          App (App (Compose (_X, OkPair (_A, _B), _B), Exr (_A, _B)), arrow_u)
       | _ -> assert false
       end
    | Var y when x = y -> Identity _X
    | Var y ->
       let arrow, _A, _B = Hashtbl.find env y in
       const_fun _X _A _B arrow
    | Literal l ->
       const _X OkFloat (Literal l)
    | Primitive p ->
       let arrow, _A, _B = primitive_to_arrow p in
       const_fun _X _A _B arrow
  in

  let term_to_arrow ((x, _) : binding) : tterm typed -> Target.t = fun t ->
    match value t with
    | Lam (binding, t) ->
       let arrow = lam_to_arrow binding t in
       Hashtbl.add env x (arrow, ok_of_typ (snd binding), ok_of_term t);
       arrow
    | _ -> assert false
  in

  source
  |> type_program_without_locations
  |> List.map (fun (binding, term) -> (binding, term_to_arrow binding term))

