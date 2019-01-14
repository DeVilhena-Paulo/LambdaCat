open Source

(** Syntax of typed terms *)

type 'a typed = {
    value : 'a;
    type' : typ
  }

type tterm = (tterm typed) Source.t


(** Typing Envronment *)
   
module Env : sig

  type t

  val empty : unit -> t

  val add : t -> identifier -> typ -> unit

  val find : t -> identifier -> typ

end = struct

  type t = (identifier, typ) Hashtbl.t

  let empty () = Hashtbl.create 13

  let add = Hashtbl.add

  let find = Hashtbl.find

end




