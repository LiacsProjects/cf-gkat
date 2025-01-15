(** A simple example decompilation algorithm
    
Used for benchmarking and testing.*)

open Common.Structures
open CFGKAT

module DecompAutOver (State : State.S) (PBool : PBool.S) = struct
  (** Decompile a GKAT automaton over `State` and `PBool` *)

  module ResExp = ExpOver (State) (PBool)
  (** The resulting expression, where each indicator is a state in the automaton *)

  module InpGKATAut = GKAT.Automaton.Make (State) (PBool)

  (** Convert a atom into a boolean expression*)
  let atom_to_b_exp (p_bools : PBool.Set.t) (at : PBool.Atom.t) : ResExp.bExp =
    let open ResExp in
    PBool.Set.fold
      (fun p_bool eb ->
        if PBool.Atom.satisfy at p_bool then And (PBool p_bool, eb)
        else And (Not (PBool p_bool), eb))
      p_bools One

  (** A trivial decompilation algorithm
    
  This algorithm assumes that the indicator doesn't contain `State.elem`
  because `State.elem` is used to indicate accept*)
  let simple_decomp (automaton : InpGKATAut.t) =
    assert (
      not @@ List.mem State.elem (InpGKATAut.get_nontrivial_states automaton));
    let open ResExp in
    let open InpGKATAut.Trans in
    IndAssign automaton.start
    |>> While
          ( Not (IndEq State.elem),
            Map.to_flat_list automaton.trans_map
            |> List.fold_left
                 (fun exp (s, at, res) ->
                   If
                     ( And (atom_to_b_exp automaton.p_bools at, IndEq s),
                       (match res with
                       | Res.Accept -> IndAssign State.elem
                       | Res.To (s, p) -> PAct p |>> IndAssign s),
                       exp ))
                 (Test Zero) )
end
