open Target

let rec arrow_list (_A : ok) (_C : ok) = function
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

let rec rebuild = fun ts ->
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

let identity_rule = function
  | `Arrow (Identity _, _, _), t -> Some [ t ]
  | t, `Arrow (Identity _, _, _) -> Some [ t ]
  | _ -> None

let curry_rule = function
  | `Arrow (Apply _, _, _), `Fork ((`Curry f) :: h, g) ->
     Some (f @ [ `Fork (h, g) ])
  | _ -> None
(*
  | `Arrow (Apply _, _, _), `Fork ([ `Curry (u :: us) ], g) ->
     let last, f' =
       List.fold_left (fun (t', acc) t -> (t, t' :: acc)) (u, []) us in
     begin match last with
     | `Arrow (Exr _, _, _) -> Some ((List.rev f') @ g)
     | _ -> None
     end
  |
  | `Arrow (Apply (_, _), _, _),
    `Fork ([ `Curry f ],
           [ `Arrow (Identity _A, _, _) ]) ->
     let id = [ `Arrow (Identity _A, _A, _A) ] in
     Some (f @ [ `Fork (id, id) ])
  | _ -> None
*)

let rec apply rule = function
  | t :: u :: tl ->
     begin match rule (t, u) with
     | Some v -> apply rule (v @ tl)
     | None -> t :: (apply rule (u :: tl))
     end
  | _ as l -> l

let rec map f t =
  f (List.map (map' f) t)
and map' f = function
  | `Fork (t, u) -> `Fork (map f t, map f u)
  | `Curry t -> `Curry (map f t)
  | `UnCurry t -> `UnCurry (map f t)
  | `Arrow _ as t -> t

let rec rewrite_term (_A : ok) (_C : ok) = fun t -> t
  |> arrow_list _A _C
  |> map (apply identity_rule)
  |> map (apply curry_rule)
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
