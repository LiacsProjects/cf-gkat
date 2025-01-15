(** Common Modules *)

module type PrintType = sig
  type t

  val pprint : t -> string
end

module type OrdPrintType = sig
  (** a type that contains order and printing*)

  include Set.OrderedType
  include PrintType with type t := t
end


module type Positive = sig
  (** A structure that behaves like a positive integer.
    
    This structure is enforced on the states of the automaton 
    to facilitate the computation of disjoint union.

    Following algebraic rule needs to be satisfied:
    - The associativity and commutativity for addition;
    - positivity: `s1 + s2 > s1`;  
    - successor: `succ s > s`;
    Notice that the inequality above are all strict.*)

  include OrdPrintType

  val one : t
  (** A element in the state *)

  val plus : t -> t -> t
  (** The additive operation, used for coproduct
        
  Coproduct requires the additive structure to be "oppsitive",
  namely `add p q > q` if `p ≠ zero`*)

  val succ : t -> t
  (** The successor function, `succ s > s`
        
  this is used to create fresh state*)

  val minus : t -> t -> t
  (** Inverse of `plus`, `p + q - q = p`*)
end

module type OfInt = sig
  type t

  val of_int : int -> t
  val to_int : t -> int
end

module type OfString = sig
  type t

  val of_string : string -> t
  val to_string : string -> t
end

module type OfIntPrint = sig
  include OfInt
  include PrintType with type t := t
end

module type OfStringPrint = sig
  include OfString
  include PrintType with type t := t
end

(** Abstraction for primitive actions 
    
PAct is just a string packaged in a module*)
module PAct : OfStringPrint = struct
  type t = string

  let of_string p = p
  let to_string p = p
  let pprint p = p
end

(** Abstraction for labels
    
which is a string packaged in a module
In the future we can make this polymorphic, 
but I am not doing that now...*)
module Label : sig
  include OrdPrintType
  include OfString with type t := t
  module Set : Set.S with type elt := t
end = struct
  type t = string

  let of_string s = s
  let to_string s = s
  let compare = String.compare
  let pprint l = l

  module Set = Set.Make (String)
end
