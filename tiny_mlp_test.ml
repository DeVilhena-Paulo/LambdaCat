(** We need to evaluate [error] defined in [tiny_mlp.j]... *)
module Eval = Tiny_mlp.Make (Category.FloatLambdaCat)
(** ... and we also need the derivative of [error]. *)
module Diff = Tiny_mlp.Make (DiffCat)

(** We study a very small MLP with two inputs, one output
    and no hidden layer. *)
type net = float * float

let make_net wxu wyu = (wxu, wyu)

let update_net (wxu, wyu) dwxu dwyu = make_net (wxu +. dwxu) (wyu +. dwyu)

(** A training set is a list of couples made of inputs and expected outputs. *)
type training_set = ((float * float) * float) list

(** A trained net must minimize the error function defined in tiny_mlp.j. *)
let acceptable_error = 0.01

let error net (input, target) =
  Eval.error ((input, net), target)

let eval_net net training_set =
  training_set |> List.map (error net) |> List.fold_left max min_float

let cost net training_set =
  let len = float_of_int (List.length training_set) in
  training_set |> List.map (error net) |> List.fold_left (+.) 0. |> fun a -> a /. len

let error_gradient net (input, target) =
  let df x y =
    DiffCat.epsilon_dapply Diff.error
      ((input, net), target)
      (((0., 0.), (x, y)), 0.) in
  df 1. 0., df 0. 1.

let cost_gradient net training_set =
  let len = float_of_int (List.length training_set) in
  let gradient_list = List.map (error_gradient net) training_set in
  let aux f =
    gradient_list |> List.map f |> List.fold_left (+.) 0. |> fun a -> a /. len in
  aux fst, aux snd

let gradient_descent ?(verbose=false) ~n_iterations ~step net training_set =
  let rec aux n net =
    begin if verbose && n mod 100 = 0 then
      let cost = cost net training_set in
      Printf.printf "%6d: (%2.5f, %2.5f) %f\n" n (fst net) (snd net) cost
    end;
    if n >= n_iterations then net else
      let dwx, dwy = cost_gradient net training_set in
      aux (n + 1) (update_net net (-.step *. dwx) (-.step *. dwy))
  in
  aux 0 net

(** [train training_set] returns a neural network trained for the
    [training_set]. *)
let train : training_set -> net =
  let rand a b = Random.init 13; (Random.float (b -. a)) +. a in
  let rand_net a b = make_net (rand a b) (rand a b) in
  gradient_descent ~n_iterations:10000 ~step:0.01 (rand_net (-.1.) 1.)

let test =
  let training_set = [ (0., 1.), 0.; (1., 0.), 1. ] in
  let trained_net = train training_set in
  let error = eval_net trained_net training_set in
  Printf.printf "eval_error trained_net training_set = %f \n" error;
  assert (eval_net trained_net training_set < acceptable_error)
