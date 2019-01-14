open Source
open Target
open Typechecker

(** [source_to_categories translates a [source] in a [target] language
    made of categorical combinators. *)
let source_to_categories : Source.program -> Target.program = fun source ->
  let (env : (identifier, Target.t) Hashtbl.t) = Hashtbl.create 13 in

  let rec lam_to_arrow ((x, ty) : binding) (ty_t : typ) : Source.term -> Target.t = function
    | App (t, u) -> failwith "Student! This is your job!"
    | Lam ((y, _), t) -> failwith "Student! This is your job!"
    | Pair (t, u) -> failwith "Student! This is your job!"
    | Fst t -> failwith "Student! This is your job!"
    | Snd t -> failwith "Student! This is your job!"
    | Var y -> failwith "Student! This is your job!"
    | Literal l -> failwith "Student! This is your job!"
    | Primitive p -> failwith "Student! This is your job!"
  in

  let term_to_arrow ((x, ty) : binding) : Source.term -> Target.t = function
    | Lam (binding, t) ->
       let arrow = lam_to_arrow binding ty t in
       Hashtbl.add env x arrow;
       arrow
    | _ -> failwith "Student! This is your job!"
  in

  List.map (fun (binding, term) -> (binding, term_to_arrow binding term)) source

