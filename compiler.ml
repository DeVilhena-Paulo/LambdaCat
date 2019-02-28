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

let make_fresh_var_gen () =
  let i = ref 0 in
  let fresh_var () =
    incr i; Id (Printf.sprintf "'a[%d]" !i) in
  fresh_var

(** [substitute x u t] substitutes all the free occurences of [x] in [t] by [u],
    that is, "t[x ↦ u]". We avoid capture by assuming that the free variables
    of [u] are all fresh. *)
let substitute (x : identifier) (u : term) : term -> term =
  let set t = function
    | Var y when x = y -> u
    | Lam ((y, _), _) when x = y -> t
    | _ as v -> v in
  traverse' (fun a -> a) set

let rec ok_of_typ : typ -> Target.ok = function
  | TyArrow (ty, ty') -> OkArrow (ok_of_typ ty, ok_of_typ ty')
  | TyPair  (ty, ty') -> OkPair  (ok_of_typ ty, ok_of_typ ty')
  | TyConstant _      -> OkFloat


(* ************************************************************************** *)
(* Translation from source to 'categorical' programs                          *)
(* ************************************************************************** *)

module Compiler (C : Context with type content = Target.t * Target.ok * Target.ok) = struct

  open Target

  include ContextMonad (C)

  let fresh_var = make_fresh_var_gen ()

  let compose (_A : ok) (_B : ok) (_C : ok) ~(g : Target.t) ~(f : Target.t) : Target.t =
    App (App (Compose (_A, _B, _C), g), f)

  let const (_X : ok) (_Y : ok) (t : Target.t) : Target.t =
    compose _X OkUnit _Y (App (UnitArrow _Y, t)) (It _X)

  let const_fun (_X : ok) (_A : ok) (_B : ok) (f : Target.t) : Target.t =
    App (Curry (_X, _A, _B), compose (OkPair (_X, _A)) _A _B f (Exr (_X, _A)))

  let rec to_arrow ((x, ty) : binding) : term -> (Target.t * ok * ok) t = function
    | App (t, u)        -> app_to_arrow (x, ty) t u
    | Lam ((y, ty'), u) -> lam_to_arrow (x, ty) (y, ty') u
    | Pair (t, u)       -> pair_to_arrow (x, ty) t u
    | Fst t             -> fst_or_snd_to_arrow true  (x, ty) t
    | Snd t             -> fst_or_snd_to_arrow false (x, ty) t
    | Var y             -> var_to_arrow (x, ty) y
    | Primitive p       -> primitive_to_arrow (x, ty) p
    | Literal l         -> literal_to_arrow (x, ty) l

  and app_to_arrow ((x, ty) : binding) (t : term) (u : term) =
    to_arrow (x, ty) t >>= fun (arrow_t, _X, _C) ->
    to_arrow (x, ty) u >>= fun (arrow_u,  _, _A)  ->
    let _, _B = get_arrow _C in
    let arrow =
      compose _X (OkPair (_C, _A)) _B
        ~g:(Apply (_A, _B)) ~f:(App (App (Fork (_X, _C, _A), arrow_t), arrow_u)) in
    return (arrow, _X, _B)

  and lam_to_arrow ((x, ty) : binding) ((y, ty') : binding) (u : term) =
    let z = fresh_var () in
    substitute y (Snd (Var z)) u |>  (* We start by [y] because [x] and [y] could be equal. *)
    substitute x (Fst (Var z))   |> fun u' ->
    to_arrow (z, TyPair (ty, ty')) u' >>= fun (arrow_u, _XxY, _C) ->
    let _X, _Y = get_pair _XxY in
    let arrow = App (Curry (_X, _Y, _C), arrow_u) in
    return (arrow, _X, OkArrow (_Y, _C))

  and pair_to_arrow ((x, ty) : binding) (t : term) (u : term) =
    to_arrow (x, ty) t >>= fun (arrow_t, _X, _A) ->
    to_arrow (x, ty) u >>= fun (arrow_u, _X, _B) ->
    let arrow = App (App (Fork (_X, _A, _B), arrow_t), arrow_u) in
    return (arrow, _X, OkPair (_A, _B))

  and fst_or_snd_to_arrow (b : bool) ((x, ty) : binding) (t : term) =
    to_arrow (x, ty) t >>= fun (arrow_t, _X, _AxB) ->
    let _A, _B = get_pair _AxB in
    let proj, _C =
      if b then Exl (_A, _B), _A else Exr (_A, _B), _B in
    let arrow =
      compose _X _AxB _C ~g:proj ~f:arrow_t in
    return (arrow, _X, _C)

  and var_to_arrow ((x, ty) : binding) (y : identifier) =
    let _X = ok_of_typ ty in
    if x = y then
      return (Identity _X, _X, _X)
    else
      lookup y >>= function
      | Some (arrow, _A, _B) ->
         return ((const_fun _X _A _B arrow), _X, OkArrow (_A, _B))
      | None -> assert false (* Excluded by typecheker. *)

  and literal_to_arrow ((_, ty) : binding) (l : literal) =
    let _X = ok_of_typ ty in
    return ((const _X OkFloat (Literal l)), _X, OkFloat)

  and primitive_to_arrow ((_, ty) : binding) (p : primitive) =
    let _X = ok_of_typ ty in
    let arrow, _A, _B =
      let ok = OkFloat in
      match p with
      | Sin | Cos | Exp | Inv | Neg ->
         (Primitive p, ok, ok)
      | Add | Mul ->
         (App (Curry (ok, ok, ok), Primitive p), ok, OkArrow (ok, ok)) in
    return ((const_fun _X _A _B arrow), _X, OkArrow (_A, _B))


  let compile_program : Source.program -> Target.program = fun source ->
    let term_to_arrow (((id, ty') : binding), (t : term)) : (binding * Target.t) t =
      match t with
      | Lam ((x, ty), t) ->
         to_arrow (x, ty) t >>= fun ((arrow_t, _, _) as arrow) ->
         add id arrow       >>= fun _                          ->
         return ((id, ty'), arrow_t)
      | _ -> assert false (* Excluded by eta expantion + parser. *) in
    run (bind_map source term_to_arrow)
      ~catch:(fun _ -> assert false (* Compilation of well-typed terms must succeed. *))

end

(** [source_to_categories] translates a [source] in a [target] language
    made of categorical combinators. *)
let source_to_categories : Source.program -> Target.program = fun source ->
  let module Compiler =
    Compiler (HashContext (struct type t = Target.t * Target.ok * Target.ok end)) in
  Compiler.compile_program source

