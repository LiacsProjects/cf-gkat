open Common.Functions
open Common.Modules
open Common.Structures

module TransOver (State : State.S) (PBool : PBool.S) = struct
  (** Defines the transition structure of GKAT automaton *)

  module Res = struct
    (* Possible results of GKAT automata transitions
       Rejection is implicit, by not present in the transition map*)
    type t = Accept | To of State.t * PAct.t

    let pprint (res : t) : string =
      match res with
      | Accept -> "Accept"
      | To (s, p) -> State.pprint s ^ ", " ^ PAct.pprint p
  end

  module Map = struct
    module Atom = PBool.Atom

    type t = Res.t Atom.Map.t State.Map.t

    (** Convert a transition map into a flattened list*)
    let to_flat_list (trans_map : t) : (State.t * Atom.t * Res.t) list =
      let ( let* ) l f = List.concat_map f l in
      let* s, at_map = State.Map.bindings trans_map in
      let* at, res = Atom.Map.bindings at_map in
      [ (s, at, res) ]

    (** A reasonable equality for transition maps *)
    let equal (map1 : t) (map2 : t) : bool =
      State.Map.equal (Atom.Map.equal ( = )) map1 map2

    let empty = State.Map.empty

    let add_flat_list (lst : (State.t * Atom.t * Res.t) list) (map : t) =
      let adding =
        List.fold_left
          (fun acc (s, at, res) ->
            State.Map.update s
              (fun at_map_opt ->
                match at_map_opt with
                | None -> Option.some @@ Atom.Map.singleton at res
                | Some at_map -> Option.some @@ Atom.Map.add at res at_map)
              acc)
          State.Map.empty lst
      in
      State.Map.union (fun _key l _r -> Some l) adding map

    let of_flat_list (lst : (State.t * Atom.t * Res.t) list) : t =
      add_flat_list lst empty

    let pprint_flat (trans_map : t) : string =
      trans_map |> to_flat_list
      (* print each transition *)
      |> List.map (fun (s, at, res) ->
             "s" ^ State.pprint s ^ ", " ^ Atom.pprint at ^ " ----> "
             ^ Res.pprint res)
      |> String.concat "\n"

    let pprint (trans_map : t) : string =
      State.Map.bindings trans_map
      |> List.map (fun (s, at_map) ->
             State.pprint s ^ "--> \n"
             ^ (Atom.Map.bindings at_map
               |> List.map (fun (at, res) ->
                      Atom.pprint at ^ " ----> " ^ Res.pprint res)
               |> String.concat "\n"))
      |> String.concat "\n"
  end
end

module Automaton = struct
  module Make (State : State.S) (PBool : PBool.S) = struct
    module Trans = TransOver (State) (PBool)
    module Atom = PBool.Atom

    module State = State
    (** expose state module*)

    type t = { p_bools : PBool.Set.t; start : State.t; trans_map : Trans.Map.t }
    (** GKAT automaton
      all the "non-trivial" states of the automaton are keys of the transMap,
      other states are implicitly transitioned to reject,
      regardless of the input atom.
      
      We do not check wether the transMap is valid, 
      it is up to the user to only use the primitive tests avalible in pBools*)

    let pprint (automata : t) : string =
      "{ NOTE: transition to rejection is implicit\nstart state:"
      ^ State.pprint automata.start
      ^ "\n"
      ^ Trans.Map.pprint automata.trans_map
      ^ "\n}"

    (** Get all the states __with transitions__ 
      
    states that always reject will be omitted*)
    let get_nontrivial_states (automaton : t) : State.t list =
      automaton.trans_map |> State.Map.bindings
      |> List.map (fun (state, _) -> state)

    (** Generate a reverse trans map,

  A state `s` will maps to all the states that can transition to `s` in exactly one transition*)
    let rev_trans_map (automaton : t) : State.t list State.Map.t =
      Trans.Map.to_flat_list automaton.trans_map
      |> List.fold_left
           (* add the result to the map one by one *)
             (fun rev_map (s, _at, res) ->
             match res with
             | Trans.Res.To (s', _) ->
                 State.Map.update s'
                   (function None -> Some [ s ] | Some lst -> Some (s :: lst))
                   rev_map
             | _ -> rev_map)
           State.Map.empty

    (** Given a flat transition list, get all the accpeting states*)
    let get_accepting_states (automaton : t) : State.t list =
      let ( let* ) l f = List.concat_map f l in
      let* s, at_map = State.Map.bindings automaton.trans_map in
      let is_accept =
        Atom.Map.exists
          (fun _at res ->
            match res with Trans.Res.Accept -> true | _ -> false)
          at_map
      in
      if is_accept then [ s ] else []

    (** Get all the live states in the automaton by reverse search from accepting states*)
    let get_live_states (automaton : t) : State.Set.t =
      let accepting_states = get_accepting_states automaton in
      let rev_map = rev_trans_map automaton in
      (* add all the live states from a live state s' to the input live states
         returns a set of new live states and a set of explored states*)
      let rec add_live_states_from (s' : State.t) (live_states : State.Set.t)
          (explored : State.Set.t) : State.Set.t * State.Set.t =
        (* if s' is already explored, backtrack*)
        if State.Set.mem s' explored then (live_states, explored)
        else
          let live_states = State.Set.add s' live_states in
          let explored = State.Set.add s' explored in
          (* find all the states that transition to s'*)
          match State.Map.find_opt s' rev_map with
          (* s' don't have any state that transtion to it*)
          | None -> (State.Set.add s' live_states, explored)
          | Some from_lst ->
              List.fold_left
                (fun (live_states, explored) s ->
                  add_live_states_from s live_states explored)
                (live_states, explored) from_lst
      in
      fst
      @@ List.fold_left
           (fun (live_states, explored) accepting_s ->
             add_live_states_from accepting_s live_states explored)
           (State.Set.empty, State.Set.empty)
           accepting_states

    (** Normalize will remove all the transition to dead state*)
    let normalize (automaton : t) : t =
      let live_states = get_live_states automaton in
      let atom_map_normalize at_map =
        Atom.Map.filter
          (fun _at res ->
            match res with
            | Trans.Res.To (s, _) -> State.Set.mem s live_states
            | _ -> true)
          at_map
      in
      {
        p_bools = automaton.p_bools;
        start = automaton.start;
        trans_map =
          automaton.trans_map
          (* remove empty atom map*)
          |> State.Map.filter_map (fun _ at_map ->
                 let at_map = atom_map_normalize at_map in
                 if Atom.Map.is_empty at_map then None else Some at_map);
      }
  end

  module Eq (State1 : State.S) (State2 : State.S) (PBool : PBool.S) = struct
    (** Heterogeneous equality between automaton*)

    module Aut1 = Make (State1) (PBool)
    module Aut2 = Make (State2) (PBool)
    module Atom = PBool.Atom

    (** Check all the possible transition results from states s1 and s2, with all atoms.
     if any result doesn't match, then return nothing,
      otherwise, return a list of states to check*)
    let check_res ((s1, a1) : State1.t * Aut1.t) ((s2, a2) : State2.t * Aut2.t)
        : (State1.t * State2.t) list option =
      let ( let* ) = Option.bind in
      let* at_map1 = State1.Map.find_opt s1 a1.trans_map in
      let* at_map2 = State2.Map.find_opt s2 a2.trans_map in
      let atoms1 = Atom.Map.keys at_map1 in
      let atoms2 = Atom.Map.keys at_map2 in
      (* if there exists some atom that rejects in map1 and not in map2, then fail,
         otherwise get the pair*)
      if atoms1 <> atoms2 then None
      else
        Atom.Set.elements atoms1
        (*We can use `find` in this step, because `atoms` is the key of these two `at_map`.*)
        |> list_filter_map_m_opt (fun atom ->
               match
                 (Atom.Map.find atom at_map1, Atom.Map.find atom at_map2)
               with
               (* success, but do not produce additional states to check*)
               | Accept, Accept -> Some None
               (* success, produce additional states to check *)
               | To (s1', p1), To (s2', p2) ->
                   if p1 = p2 then Some (Some (s1', s2')) else None
               (* fail *)
               | _ -> None)

    (** Check whether two automaton are bisimular *)
    let bisim (a1 : Aut1.t) (a2 : Aut2.t) : bool =
      (* __IMPURE__, each run will return different result,
           use with caution.
           generate a map that maps each state to the union find elem *)
      let to_elem_map1 =
        Aut1.get_nontrivial_states a1
        |> List.mapi (fun idx s -> (s, UnionFind.make idx))
        |> List.to_seq |> State1.Map.of_seq
      in
      let to_elem_map2 =
        Aut2.get_nontrivial_states a2
        |> List.mapi (fun idx s -> (s, UnionFind.make idx))
        |> List.to_seq |> State2.Map.of_seq
      in
      (*to_elem will return None only when the state is always rejecting*)
      let to_elem1_opt s = State1.Map.find_opt s to_elem_map1 in
      let to_elem2_opt s = State2.Map.find_opt s to_elem_map2 in

      (* test if two input states are equal*)
      let eq s1 s2 =
        Option.equal UnionFind.eq (to_elem1_opt s1) (to_elem2_opt s2)
      in

      let todo = Queue.create () in
      Queue.push (a1.start, a2.start) todo;

      let rec bisim_help () : bool =
        match Queue.take_opt todo with
        (* If the todo is empty, then they are bisimular *)
        | None -> true
        | Some (s1, s2) -> (
            let s1_elem_opt = to_elem1_opt s1 in
            let s2_elem_opt = to_elem2_opt s2 in
            (*return is none when the state is always rejecting*)
            match (s1_elem_opt, s2_elem_opt) with
            | None, None -> bisim_help ()
            | Some _, None -> false
            | None, Some _ -> false
            | Some s1_elem, Some s2_elem -> (
                if UnionFind.eq s1_elem s2_elem (* already equal *) then true
                else
                  match check_res (s1, a1) (s2, a2) with
                  (* mismatch exists in the results of (s1, s2) *)
                  | None -> false
                  (* mismatch doesn't exist, have states `to_check` to check*)
                  | Some to_check ->
                      (* mark s1 and s2 as equal *)
                      ignore @@ UnionFind.union s1_elem s2_elem;
                      (* remove all the states that has already been marked equal*)
                      let to_check =
                        List.filter
                          (fun (s1', s2') -> not @@ eq s1' s2')
                          to_check
                      in
                      queue_push_list todo to_check;
                      bisim_help ()))
      in
      bisim_help ()

    (** Check equivalence, normolize and check bisimularity*)
    let equiv (a1 : Aut1.t) (a2 : Aut2.t) : bool =
      let a1_n = Aut1.normalize a1 in
      let a2_n = Aut2.normalize a2 in
      bisim a1_n a2_n
  end

  module type GenSpec = sig
    (** Spec for generating an automaton *)

    val max_states_count : int
    val max_p_bools_count : int
    val max_p_act_num : int
  end

  module GenIntWith (Spec : GenSpec) = struct
    open QCheck2
    open Spec
    module IntPBool = PBool.MakeInt
    module IntState = State.MakePosInt
    module IntAut = Make (IntState) (IntPBool)
    module Trans = IntAut.Trans

    let ( let* ) = Gen.bind
    let return = Gen.return

    (** Generate all the maximium number of pbools with respect to the spec
          
      This is used in benchmarking to ensure that we are always using the same 
      amout of p_bools*)
    let all_p_bools =
      List.init max_p_bools_count (fun n -> IntPBool.of_int (n + 1))
      |> IntPBool.Set.of_list

    (** Generate some p_bools with respect to the spec
          
      This is used in testing to support shrinking*)
    let gen_p_bools : IntPBool.Set.t Gen.t =
      let* num_states = Gen.int_range 0 max_p_bools_count in
      List.init num_states (fun n -> IntPBool.of_int (n + 1))
      |> IntPBool.Set.of_list |> return

    (** Generate a primitive action with in the range defined in spec*)
    let gen_p_act : PAct.t Gen.t =
      Gen.int_range 2 (2 + max_p_act_num - 1)
      |> Gen.map (fun p -> PAct.of_string @@ "p" ^ string_of_int p)

    (** Generate a random result, 
          
      Either Accept, Reject, or transition to a state within the input*)
    let res (states : IntState.t list) : Trans.Res.t option Gen.t =
      let open Trans.Res in
      Gen.frequency
        [
          (1, Gen.return @@ Some Accept);
          (1, Gen.return None);
          ( 8,
            Gen.pair (Gen.oneofl states) gen_p_act
            |> Gen.map (fun (s, p) -> Some (To (s, p))) );
        ]

    (** Generate a fixed sized GKAT automata for benchmarking.
      
      Randomly genenrate an automaton that don't contain state 1    
      The simple decompilation algorithm requires the automaton to not contain state 1*)
    let generate_bench : IntAut.t Gen.t =
      let open Gen in
      let all_states =
        List.init max_states_count (fun n -> IntState.of_int (n + 2))
      in
      let all_atoms = IntPBool.atoms_of all_p_bools in
      let* res_opt_lst =
        Gen.list_size
          (return @@ (max_states_count * List.length all_atoms))
          (res all_states)
      in
      return
        ({
           p_bools = all_p_bools;
           start = IntState.of_int 2;
           trans_map =
             List.combine (list_prod all_states all_atoms) res_opt_lst
             |> List.filter_map (fun ((s, at), res_opt) ->
                    Option.bind res_opt (fun res -> Some (s, at, res)))
             |> Trans.Map.of_flat_list;
         }
          : IntAut.t)

    (** Generate GKAT for testing, this generation supports shrinking
              
          Generated automaton do not contain state 1, 
          since the simple decompilation algorithm do cannot take input that have 1*)
    let generate_test : IntAut.t Gen.t =
      let open Gen in
      let* states_num = int_range 1 max_states_count in
      let states = List.init states_num (fun n -> IntState.of_int (n + 2)) in
      let* p_bool_num = int_range 0 max_p_bools_count in
      let p_bools =
        List.init p_bool_num (fun n -> IntPBool.of_int n)
        |> IntPBool.Set.of_list
      in
      let atoms = IntPBool.atoms_of p_bools in
      let* res_opt_lst =
        Gen.list_size (return @@ (states_num * List.length atoms)) (res states)
      in
      return
        ({
           p_bools;
           start = IntState.of_int 2;
           trans_map =
             List.combine (list_prod states atoms) res_opt_lst
             |> List.filter_map (fun ((s, at), res_opt) ->
                    Option.bind res_opt (fun res -> Some (s, at, res)))
             |> Trans.Map.of_flat_list;
         }
          : IntAut.t)
  end
end
