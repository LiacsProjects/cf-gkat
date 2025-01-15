(** Modules for states of automaton *)

open Modules

module type S = sig
  (** Signature for state *)

  include PrintType
  include PointedCoprod.S with type t := t
  module Map : Map.S with type key := t

  val pprint_set : Set.t -> string
end

module Make (State : sig
  include PrintType
  include PointedCoprod.Base with type t := t
end) : S with type t = State.t = struct
  include State
  include PointedCoprod.Make (State)
  module Map = Map.Make (State)

  let pprint_set s = Set.elements s |> List.map pprint |> String.concat ","
end

(** Use positive integer as states

  The positivity of the integer should be enforced by the user.*)
module MakePosInt : sig
  include S
  include OfInt with type t := t
end = struct
  (** States for automaton *)
  include Make (struct
    include Int
    include PointedCoprod.MakePosInt

    let pprint (s : t) = "s" ^ string_of_int s
  end)

  let of_int s = s
  let to_int s = s
end
