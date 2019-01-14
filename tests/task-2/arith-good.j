let (sqr : float -> float) = fun (x : float) -> x * x
let (eucl_norm : (float * float) -> float) =
  fun (u : float * float) -> (sqr (fst u)) + (sqr (snd u))
let (eucl_norm_ : (float * float) -> float) = eucl_norm
let (one : float -> float) =
  fun (u : float) -> eucl_norm (sin u, cos u)

let (rebinding_test : float -> float -> float -> float) =
  fun (x : float) ->
  fun (y : float) ->
   (fun (x : float -> float) -> fun (y : float) -> x y) (fun (y : float) -> one (one x))

