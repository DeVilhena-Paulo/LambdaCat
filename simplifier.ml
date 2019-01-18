open Target


(* ************************************************************************** *)
(* Transformations                                                            *)
(* ************************************************************************** *)

(** [arrow_list _A _C t] decomposes an arrow [t] : [_A] -> [_B] into a list of
    arrows such that their composition is equal to [t] and does it recursively
    for the connectors [Fork], [Curry] and [Uncurry]. *)
let rec arrow_list (_A : ok) (_C : ok) (t : Target.t) =
  match t with
  | App (App (Compose (_, _B, _), t), u) ->
     (arrow_list _B _C t) @ (arrow_list _A _B u)
  | App (App (Fork (_, _B, _C), t), u) ->
     [ `Fork ((arrow_list _A _B t), (arrow_list _A _C u)) ]
  | App (Curry (_, _B, _C), t) ->
     [ `Curry (arrow_list (OkPair (_A, _B)) _C t) ]
  | App (UnCurry (_, _B, _C), t) ->
     [ `UnCurry (arrow_list _A (OkArrow (_B, _C)) t) ]
  | _ as t ->
     [ `Arrow (t, _A, _C) ]

(** [rebuild ts] returns a triple [(t, _A, C)] such that [ts] is equal to
    [arrow_list _A _C t]. *)
let rec rebuild ts =
  let aux (t, _B, _C) (u, _A, _) =
    (App (App (Compose (_A, _B, _C), t), u), _A, _C) in
  let arrow_list = List.map rebuild' ts in
  List.fold_left aux (List.hd arrow_list) (List.tl arrow_list)

and rebuild' = function
  | `Fork (t, u) ->
    let t', _A, _B = rebuild t in
    let u', _,  _C = rebuild u in
    App (App (Fork (_A, _B, _C), t'), u'), _A, OkPair (_B, _C)
  | `Curry t ->
    let t', _AxB, _C = rebuild t in
    let _A, _B = get_pair _AxB in
    App (Curry (_A, _B, _C), t'), _A, OkArrow (_B, _C)
  | `UnCurry t ->
    let t', _A, _BC = rebuild t in
    let _B, _C = get_arrow _BC in
    App (UnCurry (_A, _B, _C), t'), OkPair (_A, _B), _C
  | `Arrow (t, _A, _C) -> t, _A, _C


(* ************************************************************************** *)
(* Simplification rules                                                       *)
(* ************************************************************************** *)

let identity_rule = function
  | `Arrow (Identity _, _, _), t -> Some [ t ]
  | t, `Arrow (Identity _, _, _) -> Some [ t ]
  | `Fork ([ `Arrow (Exl _, _, _) ],
           [ `Arrow (Exr _, _, _) ]), t ->
     Some [ t ]
  | _ -> None

let fork_rule = function
  | `Arrow (Exl _, _, _), `Fork (t, _) -> Some t
  | `Arrow (Exr _, _, _), `Fork (_, t) -> Some t
  | _ -> None

let curry_rule = function
  | `Arrow (Apply _, _, _), `Fork ([ `Curry f ], g) ->
     let _, _A, _ = rebuild g in
     let h = [ `Arrow (Identity _A, _A, _A) ] in
     Some (f @ [ `Fork (h, g) ])
  | `Arrow (Apply _, _, _), `Fork ((`Curry f) :: h, g) ->
     Some (f @ [ `Fork (h, g) ])
  | _ -> None


(* ************************************************************************** *)
(* Simplification procedure                                                   *)
(* ************************************************************************** *)

(** [apply rule ts] search for pair of consecutive terms in the list [ts] that
    will match [rule] and returns this new rewritten list together with a boolean
    flag that is true iff the simplification rule was applied one or more times. *)
let apply rule = fun ts ->
  let rec apply' flag = function
    | t :: u :: tl ->
       begin match rule (t, u) with
       | Some v ->
          apply' true (v @ tl)
       | None ->
          let ts', flag' =
            apply' flag (u :: tl) in
          t :: ts', flag'
       end
    | _ as l -> l, flag in
  apply' false ts

(** [map f t] applies f recursively on t. *)
let rec map f t =
  f (List.map (map' f) t)

and map' f = function
  | `Fork (t, u) -> `Fork (map f t, map f u)
  | `Curry t -> `Curry (map f t)
  | `UnCurry t -> `UnCurry (map f t)
  | `Arrow _ as t -> t

let saturate rules =
  let apply' flag rule = fun ts ->
    let ts', flag' = apply rule ts in
    flag := !flag || flag';
    ts' in
  let aux flag t =
    flag := false;
    List.fold_left (fun t' rule -> map (apply' flag rule) t') t rules in
  let flag = ref true in
  let rec saturate' t =
    if !flag then saturate' (aux flag t) else t in
  saturate'

let rec rewrite_term (_A : ok) (_C : ok) = fun t -> t
  |> arrow_list _A _C
  |> saturate [ identity_rule; fork_rule; curry_rule ]
  |> rebuild

(** [rewrite defs] applies category laws to remove [apply] and [curry]
    from the compiled programs. *)
let rewrite : Target.program -> Target.program = fun defs ->
  if !Options.simplify then
    List.map (fun ((x, ty) as binding, t) ->
        let _A, _C = get_arrow (Compiler.ok_of_typ ty) in
        let t', _, _ = rewrite_term _A _C t in
        (binding, t'))
      defs
  else
    defs
