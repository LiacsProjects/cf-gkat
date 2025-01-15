(** Values and Types related to PBools *)

open Modules

module Atom = struct
  module type S = sig
    type p_bool

    include OrdPrintType

    val satisfy : t -> p_bool -> bool

    val make_pos : p_bool -> t -> t
    (** make an p_bool in atom positive *)

    val of_list: p_bool list -> t 
    (** return a atom where only the given atom is true*)

    val bot : t
    (** bottom, where all the p_bools are false*)

    module Set : Set.S with type elt := t

    module Map : sig
      include Map.S with type key := t

      val keys : 'a t -> Set.t
    end
  end

  module MakeSet (PBoolType : OrdPrintType) : S with type p_bool = PBoolType.t =
  struct
    (** A atom is a set of p_bools that appears positively in the atom*)

    type p_bool = PBoolType.t

    module SetAtom = Set.Make (PBoolType)
    include SetAtom

    let satisfy at b = mem b at
    let bot = SetAtom.empty
    let make_pos = SetAtom.add

    let pprint at =
      if is_empty at then "{}"
      else at |> elements |> List.map PBoolType.pprint |> String.concat "⋅"

    module Set = Set.Make (SetAtom)

    module Map = struct
      include Map.Make (SetAtom)

      let keys (map : 'a t) : Set.t =
        bindings map |> List.map (fun (key, _) -> key) |> Set.of_list
    end
  end
end

module type S = sig
  include OrdPrintType

  module Set : sig
    include Set.S with type elt := t

    val pprint : t -> string
  end

  module Map : Map.S with type key := t
  module Atom : Atom.S with type p_bool := t

  val atoms_of : Set.t -> Atom.t list
  (** Generate all the truth assignment to all the prmitive tests in the input set
      
  The p_bools that are not in the set will always be negative*)

end

module Make (PBool : OrdPrintType) : S with type t = PBool.t = struct
  include PBool

  module Set = struct
    include Set.Make (PBool)

    let pprint s = elements s |> List.map pprint |> String.concat ","
  end

  module Map = Map.Make (PBool)
  module Atom = Atom.MakeSet (PBool)

  (** Gather all the atom with respect to a set of p_bools
      
  the primitive tests outside of the input set will always appear negative*)
  let rec atoms_of (p_bools : Set.t) : Atom.t list =
    match Set.choose_opt p_bools with
    | None -> [ Atom.bot ]
    | Some p_bool ->
        let atoms_of_rest = atoms_of (Set.remove p_bool p_bools) in
        (*atoms where `p_bool` is negative*)
        atoms_of_rest
        @ (*atoms where `p_bool` is positive*)
        (atoms_of_rest |> List.map (fun at -> Atom.make_pos p_bool at))
end

module MakeInt : sig
  include S
  include OfInt with type t := t
end = struct
  include Make (struct
    include Int

    let pprint b = "b" ^ string_of_int b
  end)

  let of_int b = b
  let to_int b = b
end


module MakeString : sig
  include S
  include OfString with type t := t
end = struct
  include Make (struct
    include String

    let pprint b = b
  end)

  let of_string b = b
  let to_string b = b
end
