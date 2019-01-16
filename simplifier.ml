open Target


let identity_rule : Target.t * Target.t -> Target.t option = function
  | Identity _, t -> Some t
  | t, Identity _ -> Some t
  | _ -> None

let curry_rule : Target.t * Target.t -> Target.t option = function
  | Apply _, App (App (Fork _, App (App (Compose _, App (Curry _, f)), Exl _)), Exr _) -> Some f
  | Apply _, App (App (Fork _, App (Curry (_X, _A, _B), f)), Identity _) when _X = _A ->
     let id = Identity _A in
     let _AxA = OkPair (_A, _A) in
     Some (App (App (Compose (_A, _AxA, _B), f), App (App (Fork (_A, _A, _B), id), id)))
  | _ -> None

(*
let rec arrow_list (_A : ok) (_C : ok) = function
  | App (App (Compose (_, _B, _), t), u) ->
     [ `Compose ((arrow_list' _B _C t) @ (arrow_list' _A _B u)) ]
  | App (App (Fork (_, _B, _C), t), u) ->
     [ `Fork ((arrow_list _A _B t), (arrow_list _A _C u)) ]
  | App (Curry (_, _B, _C), t) ->
     [ `Curry (arrow_list (OkPair (_A, _B)) _C t) ]
  | App (UnCurry (_, _B, _C), t) ->
     [ `UnCurry (arrow_list _A (OkArrow (_B, _C)) t) ]
  | _ as t ->
     [ `Arrow (t, _A, _C) ]
and arrow_list' (_A : ok) (_C : ok) t =
  match (arrow_list _A _C t) with
  | [ `Compose t' ] -> t'
  | _ as t' -> t'
 *)
let rec arrow_list (_A : ok) (_C : ok) = function
  | App (App (Compose (_, _B, _), t), u) -> (arrow_list _B _C t) @ (arrow_list _A _B u)
  | _ as t -> [ (t, _A, _C) ]

(*
  let rec arrow_list' _A _C acc = function
  | App (App (Compose (_, _B, _), t), u) -> arrow_list' _B _C (arrow_list' _A _B acc t) u
  | _ as t -> acc @ [ (t, _A, _C) ] in
  arrow_list' _A _C []
 *)

let compose : (Target.t * ok * ok) list -> Target.t = fun arrow_list ->
  let aux (t, _B, _C) (u, _A, _) =
    (App (App (Compose (_A, _B, _C), t), u), _A, _C) in
  let output, _, _ =
    List.fold_left aux (List.hd arrow_list) (List.tl arrow_list) in
  output

let rec apply rule : (Target.t * ok * ok) list -> (Target.t * ok * ok) list = function
  | ((t, _, _C) as t') :: ((u, _A, _) as u') :: tl ->
     begin match rule (t, u) with
     | Some v -> apply rule ((arrow_list _A _C v) @ tl)
     | None -> t' :: (apply rule (u' :: tl))
     end
  | _ as l -> l


let rec rewrite_term (_A : ok) (_C : ok) : Target.t -> Target.t = fun t -> t
  |> arrow_list _A _C
  |> List.map (fun (t, _A, _C) -> (rewrite_term _A _C t, _A, _C))
  |> apply identity_rule
  |> apply curry_rule
  |> apply identity_rule
  |> compose

(** [rewrite defs] applies category laws to remove [apply] and [curry]
    from the compiled programs. *)
let rewrite : Target.program -> Target.program = fun defs ->
  if !Options.simplify then
    List.map (fun ((x, ty) as binding, t) ->
        let ok =
          match Compiler.ok_of_typ ty with
           | OkArrow (a, b) -> (a, b)
           | _ -> assert false
        in
        (binding, rewrite_term (fst ok) (snd ok) t))
      defs
  else
    defs
