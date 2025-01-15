open Modules

module type S = sig
  include PointedCoprod.S
  include PrintType with type t := t
end

module MakePosInt : sig
  include S
  include OfInt with type t := t
end = struct
  include PointedCoprod.MakePosInt

  let pprint i = string_of_int i
  let of_int i = i
  let to_int i = i
end
