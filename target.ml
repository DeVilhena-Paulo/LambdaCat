type program = (Source.binding * t) list

and t =
  | App of t * t
  | Identity of ok
  | Curry of ok * ok * ok
  | UnCurry of ok * ok * ok
  | Apply of ok * ok
  | Fork of ok * ok * ok
  | Exl of ok * ok
  | Exr of ok * ok
  | UnitArrow of ok
  | It of ok
  | Compose of ok * ok * ok
  | Literal of Source.literal
  | Primitive of Source.primitive
and ok =
  | OkFloat
  | OkUnit
  | OkPair of ok * ok
  | OkArrow of ok * ok

let get_pair : ok -> (ok * ok) = function
  | OkPair (a, b) -> (a, b)
  | _ -> raise (Failure "get_pair")

let get_arrow : ok -> (ok * ok) = function
  | OkArrow (a, b) -> (a, b)
  | _ -> raise (Failure "get_arrow")
