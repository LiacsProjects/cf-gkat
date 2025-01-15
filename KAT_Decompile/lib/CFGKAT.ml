open Common.Functions
open Common.Structures
open Common.Modules

module TransOver (Ind : Ind.S) (State : State.S) (PBool : PBool.S) = struct
  (** transitions for CF-GKAT automaton and CF-GKAT automaton with start pseudo-state *)

  module Res = struct
    (** Result of a transition, 
      
     `Ind` repersents accept and output the final indicator value*)
    type t =
      | Reject
      | Acc of Ind.t
      | To of Ind.t * State.t * PAct.t
      | Brk of Ind.t
      | Ret
      | Goto of Label.t

    let pprint (res : t) : string =
      match res with
      | Reject -> "Reject"
      | Acc i' -> "Accept with ind " ^ Ind.pprint i'
      | To (i', s', p) ->
          "to " ^ Ind.pprint i' ^ ", " ^ State.pprint s' ^ ", " ^ PAct.pprint p
      | Brk i' -> "Break with ind " ^ Ind.pprint i'
      | Ret -> "Returns"
      | Goto l -> "Goto " ^ Label.pprint l
  end

  module PState = struct
    (** psuedo-state *)

    type t = Ind.t -> PBool.Atom.t -> Res.t

    let pprint (inds : Ind.Set.t) (states : State.Set.t) (p_bools : PBool.Set.t)
        (p_state : t) : string =
      list_prod (Ind.Set.elements inds)
        (list_prod (State.Set.elements states) (PBool.atoms_of p_bools))
      |> List.map (fun (i, (s, at)) ->
             Ind.pprint i ^ ", " ^ State.pprint s ^ ", " ^ PBool.Atom.pprint at
             ^ " -----> "
             ^ Res.pprint (p_state i at))
      |> String.concat "\n"

    (** uniform continuation of two pseudo-state
        
    Connect all the accepting transition of `p_state1` to `p_state2`*)
    let uni_cont (p_state1 : t) (p_state2 : t) : t =
     fun i at ->
      match p_state1 i at with Acc i' -> p_state2 i' at | res -> res
  end

  module Func = struct
    type t = State.t -> PState.t

    let pprint (inds : Ind.Set.t) (states : State.Set.t) (p_bools : PBool.Set.t)
        (trans : t) : string =
      list_prod (Ind.Set.elements inds)
        (list_prod (State.Set.elements states) (PBool.atoms_of p_bools))
      |> List.map (fun (i, (s, at)) ->
             Ind.pprint i ^ ", " ^ State.pprint s ^ ", " ^ PBool.Atom.pprint at
             ^ " -----> "
             ^ Res.pprint (trans s i at))
      |> String.concat "\n"
  end

  module Jump = struct
    (** the jump map, where each label is mapped to its entry point
        
    For labels that are not in the program, it will be mapped to the constant reject pseudo-state.*)

    type t = Label.t -> PState.t

    let pprint (labels : Label.Set.t) (inds : Ind.Set.t) (p_bools : PBool.Set.t)
        (jumps : t) : string =
      Label.Set.elements labels
      |> List.map (fun l ->
             list_prod (Ind.Set.elements inds) (PBool.atoms_of p_bools)
             |> List.map (fun (i, at) ->
                    Label.pprint l ^ ", " ^ Ind.pprint i ^ ", "
                    ^ PBool.Atom.pprint at ^ " => "
                    ^ Res.pprint (jumps l i at))
             |> String.concat "\n")
      |> String.concat "\n"
  end
end

module Automaton = struct
  module Make (Ind : Ind.S) (State : State.S) (PBool : PBool.S) = struct
    module Trans = TransOver (Ind) (State) (PBool)

    type t = {
      states : State.Set.t;
      inds : Ind.Set.t;
      labels : Label.Set.t;
      p_bools : PBool.Set.t;
      start : State.t;
      trans : Trans.Func.t;
      jumps : Trans.Jump.t;
    }

    (** pairs of indicator value and state of current automaton as a new State type
        
    The state of the resulting automaton of `to_GKAT_automaton` function*)
    module ResGKATState = Common.Structures.State.Make (struct
      include PointedCoprod.MakePair (Ind) (State)

      let pprint (s1, s2) = "(" ^ Ind.pprint s1 ^ ", " ^ State.pprint s2 ^ ")"
    end)

    module JumpMap = Map.Make (struct
      type t = Label.t * Ind.t * PBool.Atom.t

      let compare = compare
    end)

    let resolve_jumps (jumps : Trans.Jump.t) (labels : Label.Set.t)
        (atoms : PBool.Atom.t list) (indicators : Ind.t list) : Trans.Jump.t =
      let open Trans.Res in
      let compute_rec i at compute_opt l =
        match jumps l i at with
        | Goto l' -> (
            match compute_opt l' with None -> Reject | Some res -> res)
        | res -> res
      in
      let jump_list =
        let ( let* ) l f = List.concat_map f l in
        let* at = atoms in
        let* i = indicators in
        let* l, res =
          compute_map_rec (compute_rec i at) (Label.Set.elements labels)
        in
        [ ((l, i, at), res) ]
      in
      let jump_map = JumpMap.of_seq (List.to_seq jump_list) in
      fun l i at ->
        if Label.Set.mem l labels then
          JumpMap.find_opt (l, i, at) jump_map |> Option.value ~default:Reject
        else Reject

    module ResGKATAut = GKAT.Automaton.Make (ResGKATState) (PBool)
    (** GKAT automaton where the states are pairs of indicator value and state of current automaton
        
    Resulting automaton of the `to_GKAT_automaton` function*)

    (** Convert a CF-GKAT automata to a GKAT automata given a starting indicator
        
    The results only contains states that are reachable from start*)
    let to_GKAT_automaton (start_i : Ind.t) (a : t) : ResGKATAut.t =
      let open ResGKATAut.Trans.Res in
      let atoms = PBool.atoms_of a.p_bools in
      let jumps l =
        resolve_jumps a.jumps a.labels (PBool.atoms_of a.p_bools)
          (Ind.Set.elements a.inds) l
      in
      let module IndStateSet = Set.Make (struct
        type t = Ind.t * State.t

        let compare = compare
      end) in
      (* add all the transition map from reachable state of s to the input trans map
         return a new trans map and a set of explored states*)
      let rec add_trans_from ((i, s) : Ind.t * State.t)
          (trans_map : ResGKATAut.Trans.Map.t) (explored : IndStateSet.t) :
          ResGKATAut.Trans.Map.t * IndStateSet.t =
        (* print_endline
           ("adding transaction from " ^ string_of_int i ^ ", " ^ State.pprint s); *)
        if IndStateSet.mem (i, s) explored then
          ((* print_endline "already explored"; *)
           trans_map, explored)
        else
          (* construct new explored set and new transition map *)
          let explored = IndStateSet.add (i, s) explored in
          let trans_flat_lst =
            List.filter_map
              (fun at ->
                match a.trans s i at with
                | Acc _ -> Some ((i, s), at, Accept)
                | To (i', s', p) -> Some ((i, s), at, To ((i', s'), p))
                | Reject -> None
                | Brk _ -> failwith "Break on the top level"
                | Ret -> Some ((i, s), at, Accept)
                | Goto l -> (
                    match jumps l i at with
                    | Acc _ -> Some ((i, s), at, Accept)
                    | To (i', s', p) -> Some ((i, s), at, To ((i', s'), p))
                    | Reject -> None
                    | Brk _ -> failwith "Break on the top level"
                    | Ret -> Some ((i, s), at, Accept)
                    | Goto _ -> failwith ("Unresolved goto: " ^ Label.pprint l)))
              atoms
          in
          let trans_map =
            ResGKATAut.Trans.Map.add_flat_list trans_flat_lst trans_map
          in
          (* print_endline
              ("new trans map after adding " ^ string_of_int i ^ ", "
             ^ State.pprint s ^ ":\n"
              ^ GKAT.Trans.pprint_map trans_map); *)
          (* set that is reachable from (i,s)*)
          let to_lst =
            List.filter_map
              (fun at ->
                match a.trans s i at with
                | To (i', s', _p) -> Some (i', s')
                | Goto l -> (
                    match jumps l i at with
                    | To (i', s', _p) -> Some (i', s')
                    | Goto _ -> failwith ("Unresolved goto: " ^ Label.pprint l)
                    | _ -> None)
                | _ -> None)
              atoms
          in
          List.fold_left
            (fun (trans_map, explored) (i', s') ->
              add_trans_from (i', s') trans_map explored)
            (trans_map, explored) to_lst
      in
      {
        p_bools = a.p_bools;
        start = (start_i, a.start);
        trans_map =
          fst
          @@ add_trans_from (start_i, a.start) ResGKATAut.Trans.Map.empty
               IndStateSet.empty;
      }
  end
end

module AutomatonPStart = struct
  (**This module implement CF-GKAT automata with start psuedo-state*)

  module Make (Ind : Ind.S) (State : State.S) (PBool : PBool.S) = struct
    module Trans = TransOver (Ind) (State) (PBool)
    module PState = Trans.PState

    type t = {
      states : State.Set.t;
      inds : Ind.Set.t;
      labels : Label.Set.t;
      p_bools : PBool.Set.t;
      p_start : PState.t;
      trans : Trans.Func.t;
      jumps : Trans.Jump.t;
    }

    let p_start_pprint (inds : Ind.Set.t) (p_bools : PBool.Set.t)
        (p_start : PState.t) : string =
      list_prod (Ind.Set.elements inds) (PBool.atoms_of p_bools)
      |> List.map (fun (i, at) ->
             Ind.pprint i ^ ", " ^ PBool.Atom.pprint at ^ " -----> "
             ^ Trans.Res.pprint @@ p_start i at)
      |> String.concat "\n"

    let pprint (a : t) : string =
      "{\np_bools: " ^ PBool.Set.pprint a.p_bools ^ "\nstates: "
      ^ State.pprint_set a.states ^ "\np_start:\n"
      ^ p_start_pprint a.inds a.p_bools a.p_start
      ^ "\ntrans_map:\n"
      ^ Trans.Func.pprint a.inds a.states a.p_bools a.trans
      ^ "\njumps:\n"
      ^ Trans.Jump.pprint a.labels a.inds a.p_bools a.jumps
      ^ "\n}"

    type coprodRes = {
      states : State.Set.t;
      left_start : PState.t;
      right_start : PState.t;
      trans : Trans.Func.t;
      jump : Trans.Jump.t;
      is_left : State.t -> bool;
    }
    (** Helper type for the coproduct function, result of coproduct of two automaton *)

    (** coproduct of two automaton
  
      The make_start function will contruct a new start from the original starts.
      returns a combined automaton, and a function to test whether a state is a left state.*)
    let coprod (left_a : t) (right_a : t) : coprodRes =
      assert (left_a.p_bools = right_a.p_bools);
      assert (left_a.inds = right_a.inds);
      assert (Label.Set.inter left_a.labels right_a.labels == Label.Set.empty);
      let open Trans.Res in
      let coprod_util, coprod_states =
        State.coprod_with_dom left_a.states right_a.states
      in
      let to_left_res res =
        match res with
        | To (i', s', p) -> To (i', coprod_util.to_left s', p)
        | res -> res
      in
      let to_right_res res =
        match res with
        | To (i', s', p) -> To (i', coprod_util.to_right s', p)
        | res -> res
      in
      let left_start i at = to_left_res @@ left_a.p_start i at in
      let right_start i at = to_right_res @@ right_a.p_start i at in
      let coprod_trans s i at =
        match coprod_util.from_coprod s with
        | Left s -> to_left_res @@ left_a.trans s i at
        | Right s -> to_right_res @@ right_a.trans s i at
      in
      let coprod_jump l i at =
        if Label.Set.mem l left_a.labels then to_left_res @@ left_a.jumps l i at
        else if Label.Set.mem l right_a.labels then
          to_right_res @@ right_a.jumps l i at
        else Reject (* non-existent label *)
      in
      {
        states = coprod_states;
        left_start;
        right_start;
        trans = coprod_trans;
        jump = coprod_jump;
        is_left = coprod_util.is_left;
      }

    (** Resolve all the breaks into accept
        
    This resolution is used when converting loops*)
    let resolve_break (p_state : PState.t) : PState.t =
     fun i at -> match p_state i at with Brk i' -> Acc i' | res -> res

    module MidAutomaton = Automaton.Make (Ind) (State) (PBool)

    (** Convert a CF-GKAT automaton with pseudo-start to a CF-GKAT automaton*)
    let to_mid_automaton (a_p_start : t) : MidAutomaton.t =
      let new_start = State.fresh a_p_start.states in
      {
        inds = a_p_start.inds;
        p_bools = a_p_start.p_bools;
        labels = a_p_start.labels;
        states = State.Set.add new_start a_p_start.states;
        start = new_start;
        trans =
          (fun s i at ->
            if s = new_start then a_p_start.p_start i at
            else a_p_start.trans s i at);
        jumps = a_p_start.jumps;
      }

    module ResGKATAut = MidAutomaton.ResGKATAut
    (** Resulting GKAT automaton from the to_GKAT_automaton function*)

    module ResGKATState = MidAutomaton.ResGKATState
    (** Resulting state from the to_GKAT_automaton function*)

    (** Convert a GKATI automaton with start pseudo-state to a trace equivalent
      GKAT automaton, when given a staring indicator `start_i`*)
    let to_GKAT_automaton (start_i : Ind.t) (a : t) : ResGKATAut.t =
      (* print_endline
          ("converting to GKAT automaton with starting indicator "
         ^ string_of_int start_i ^ ":\n" ^ pprint a); *)
      a |> to_mid_automaton |> MidAutomaton.to_GKAT_automaton start_i
  end
end

module ExpOver (Ind : Ind.S) (PBool : PBool.S) = struct
  (** Indicator value *)

  type bExp =
    | PBool of PBool.t
    | Zero
    | One
    | IndEq of Ind.t
    | Or of bExp * bExp
    | And of bExp * bExp
    | Not of bExp

  type t =
    | Test of bExp
    | PAct of PAct.t
    | IndAssign of Ind.t
    | Seq of t * t
    | If of bExp * t * t
    | While of bExp * t
    | Break
    | Return
    | Goto of Label.t
    | Label of Label.t

  (** shorthand for sequencing commands *)
  let ( |>> ) (e1 : t) (e2 : t) : t = Seq (e1, e2)

  (** Tests whether an atom and an indicator satisfy a boolean expression*)
  let rec satisfy (i : Ind.t) (at : PBool.Atom.t) (b_exp : bExp) : bool =
    match b_exp with
    | PBool b -> PBool.Atom.satisfy at b
    | Zero -> false
    | One -> true
    | IndEq i' -> i = i'
    | Or (eb1, eb2) -> satisfy i at eb1 || satisfy i at eb2
    | And (eb1, eb2) -> satisfy i at eb1 && satisfy i at eb2
    | Not eb -> not @@ satisfy i at eb

  let rec p_bools_of_bexp (b_exp : bExp) : PBool.Set.t =
    match b_exp with
    | PBool b -> PBool.Set.singleton b
    | Or (eb1, eb2) ->
        PBool.Set.union (p_bools_of_bexp eb1) (p_bools_of_bexp eb2)
    | And (eb1, eb2) ->
        PBool.Set.union (p_bools_of_bexp eb1) (p_bools_of_bexp eb2)
    | IndEq _ -> PBool.Set.empty
    | Zero -> PBool.Set.empty
    | One -> PBool.Set.empty
    | Not eb -> p_bools_of_bexp eb

  (** Get all the indicators in a boolean expression*)
  let rec inds_of_bexp (b_exp : bExp) : Ind.Set.t =
    match b_exp with
    | PBool _ -> Ind.Set.empty
    | IndEq i -> Ind.Set.singleton i
    | Zero -> Ind.Set.empty
    | One -> Ind.Set.empty
    | Or (eb1, eb2) -> Ind.Set.union (inds_of_bexp eb1) (inds_of_bexp eb2)
    | And (eb1, eb2) -> Ind.Set.union (inds_of_bexp eb1) (inds_of_bexp eb2)
    | Not eb -> inds_of_bexp eb

  (** Extract the primitive tests used in the given CF-GKAT expression*)
  let rec p_bools_of (exp : t) : PBool.Set.t =
    match exp with
    | Test eb -> p_bools_of_bexp eb
    | PAct _ -> PBool.Set.empty
    | IndAssign _ -> PBool.Set.empty
    | Seq (e1, e2) -> PBool.Set.union (p_bools_of e1) (p_bools_of e2)
    | If (eb, e1, e2) ->
        PBool.Set.union (p_bools_of_bexp eb)
          (PBool.Set.union (p_bools_of e1) (p_bools_of e2))
    | While (eb, e) -> PBool.Set.union (p_bools_of_bexp eb) (p_bools_of e)
    | Break -> PBool.Set.empty
    | Return -> PBool.Set.empty
    | Goto _ -> PBool.Set.empty
    | Label _ -> PBool.Set.empty

  let rec inds_of (exp : t) : Ind.Set.t =
    match exp with
    | Test eb -> inds_of_bexp eb
    | PAct _ -> Ind.Set.empty
    | IndAssign i -> Ind.Set.singleton i
    | Seq (e1, e2) -> Ind.Set.union (inds_of e1) (inds_of e2)
    | If (eb, e1, e2) ->
        Ind.Set.union (inds_of_bexp eb)
          (Ind.Set.union (inds_of e1) (inds_of e2))
    | While (eb, e) -> Ind.Set.union (inds_of_bexp eb) (inds_of e)
    | Break -> Ind.Set.empty
    | Return -> Ind.Set.empty
    | Goto _ -> Ind.Set.empty
    | Label _ -> Ind.Set.empty

  let parenthesize s = "(" ^ s ^ ")"

  let pprint_bexp (bexp : bExp) : string =
    let rec pprint_with_precedence bexp =
      match bexp with
      | PBool b -> (PBool.pprint b, 0)
      | Zero -> ("false", 0)
      | One -> ("true", 0)
      | IndEq i -> ("x == " ^ Ind.pprint i, 0)
      | Not b ->
          let b_str, b_precedence = pprint_with_precedence b in
          if b_precedence <= 1 then ("¬" ^ b_str, 1)
          else ("¬ " ^ parenthesize @@ b_str, 1)
      | And (b1, b2) ->
          let b1_str, b1_precedence = pprint_with_precedence b1 in
          let b2_str, b2_precedence = pprint_with_precedence b2 in
          if b1_precedence <= 2 && b2_precedence <= 2 then
            (b1_str ^ " ∧ " ^ b2_str, 2)
          else if b1_precedence > 2 && b2_precedence <= 2 then
            (parenthesize b1_str ^ " ∧ " ^ b2_str, 2)
          else if b1_precedence <= 2 && b2_precedence > 2 then
            (b1_str ^ " ∧ " ^ parenthesize b2_str, 2)
          else (parenthesize b1_str ^ "∧" ^ parenthesize b2_str, 2)
      | Or (b1, b2) ->
          let b1_str, b1_precedence = pprint_with_precedence b1 in
          let b2_str, b2_precedence = pprint_with_precedence b2 in
          if b1_precedence <= 3 && b2_precedence <= 3 then
            (b1_str ^ " ∨ " ^ b2_str, 1)
          else if b1_precedence > 3 && b2_precedence <= 3 then
            (parenthesize b1_str ^ "∨" ^ b2_str, 3)
          else if b1_precedence <= 3 && b2_precedence > 3 then
            (b1_str ^ " ∨ " ^ parenthesize b2_str, 3)
          else (parenthesize b1_str ^ " ∨ " ^ parenthesize b2_str, 3)
    in
    fst @@ pprint_with_precedence bexp

  let rec pprint (exp : t) : string =
    match exp with
    | Test b -> pprint_bexp b
    | PAct p -> PAct.pprint p
    | IndAssign i -> "x := " ^ Ind.pprint i
    | Seq (e1, e2) -> pprint e1 ^ "; " ^ pprint e2
    | If (b, e1, e2) ->
        "if " ^ pprint_bexp b ^ " then " ^ pprint e1 ^ " else " ^ pprint e2
        ^ " endif"
    | While (b, e) -> "while " ^ pprint_bexp b ^ " do " ^ pprint e ^ " endwhile"
    | Break -> "break"
    | Return -> "return"
    | Goto l -> "goto " ^ Label.pprint l
    | Label l -> "label " ^ Label.pprint l

  module ToAutomatonWith (State : State.S) = struct
    (**A suite of function to convert a expression to a CF-GKAT automaton
        
    The functor takes in a `StateType` where it specifies the type of the state*)

    module AutomatonPStart = AutomatonPStart.Make (Ind) (State) (PBool)

    module State = State
    (** expose the state type *)

    (** psuedo-start as a map *)
    module PStartMap = Map.Make (struct
      type t = Ind.t * PBool.Atom.t

      let compare = compare
    end)

    (** The γ function in the original paper, 
      
      Resolves "unproductive" infinite loop for while loop:
      infintie loops without executing any action will be directly rejected *)
    let resolve_loop (b_exp : bExp) (body_start : AutomatonPStart.PState.t)
        (atoms : PBool.Atom.t list) (indcators : Ind.t list) :
        AutomatonPStart.PState.t =
      let open AutomatonPStart in
      let open Trans.Res in
      (* Compute the result for i, where compute_i_opt is the recursion *)
      let compute_i_rec at compute_i_opt i =
        match (satisfy i at b_exp, body_start i at) with
        (* do not satisfy the boolean expression, exit loop*)
        | false, _ -> Acc i
        (* recursion case *)
        | true, Acc i' -> (
            (* `compute_i_opt i'` will return None when a infinite loop is detected,
               in that case we will reject *)
            match compute_i_opt i' with None -> Reject | Some res -> res)
        (* body executes a primitive action *)
        | true, To (i', s, p) -> To (i', s, p)
        (* notice that the break is not resolved here,
           it will be resolved later, following the structure of the paper*)
        | true, res -> res
      in
      let p_start_list =
        let ( let* ) l f = List.concat_map f l in
        let* at = atoms in
        let* i, res = compute_map_rec (compute_i_rec at) indcators in
        [ ((i, at), res) ]
      in
      let p_start_map = PStartMap.of_seq (List.to_seq p_start_list) in
      fun i at ->
        PStartMap.find_opt (i, at) p_start_map |> Option.value ~default:Reject

    (** Thompsons construction, covert a CF-GKAT exp to a CF-GKAT automata with pseudo-start
      
      NOTE: this contruction will always produce automaton 
      with "positive" (greater than zeor) state,
      this helps with coproduct and uniform continuation*)
    let rec thomp_contr (inds : Ind.Set.t) (p_bools : PBool.Set.t) (exp : t) :
        AutomatonPStart.t =
      let open AutomatonPStart in
      match exp with
      | Test eb ->
          {
            inds;
            p_bools;
            labels = Label.Set.empty;
            states = State.Set.empty;
            p_start = (fun i at -> if satisfy i at eb then Acc i else Reject);
            (* transiton don't matter since we have a empty state set *)
            trans = (fun _ _ _ -> Reject);
            jumps = (fun _ _ _ -> Reject);
          }
      | PAct p ->
          (* the only state in this automaton
             it cannot be zero, since the states in the automaton has to be positive *)
          let s1 = State.elem in
          {
            inds;
            p_bools;
            labels = Label.Set.empty;
            (* ensuring that the state is positive *)
            states = State.Set.singleton @@ s1;
            p_start = (fun i _ -> To (i, s1, p));
            (* this transition will accept all the input *)
            trans = (fun _ i _ -> Acc i);
            jumps = (fun _ _ _ -> Reject);
          }
      | IndAssign i' ->
          {
            inds;
            p_bools;
            labels = Label.Set.empty;
            states = State.Set.empty;
            p_start = (fun _ _ -> Acc i');
            trans = (fun _ _ _ -> Reject);
            jumps = (fun _ _ _ -> Reject);
          }
      | Seq (e1, e2) ->
          let a1 = thomp_contr inds p_bools e1 in
          let a2 = thomp_contr inds p_bools e2 in
          (* print_endline "sequencing: ";
             print_endline ("e1 converted to: "^pprint a1);
             print_endline ("e2 converted to: "^pprint a2); *)
          let coprod_res = coprod a1 a2 in
          {
            states = coprod_res.states;
            inds;
            labels = Label.Set.union a1.labels a2.labels;
            p_bools;
            p_start = PState.uni_cont coprod_res.left_start coprod_res.right_start;
            trans =
              (fun s ->
                if coprod_res.is_left s then
                  PState.uni_cont (coprod_res.trans s) coprod_res.right_start
                else coprod_res.trans s);
            jumps =
              (fun l ->
                (* if the jump is in a1, then continue it with ι2 (right_start)
                   otherwise (either the jump is in a2, or the label don't exists)
                   keep the result *)
                if Label.Set.mem l a1.labels then
                  PState.uni_cont (coprod_res.jump l) coprod_res.right_start
                else coprod_res.jump l);
          }
      | If (eb, e1, e2) ->
          let a1 = thomp_contr inds p_bools e1 in
          let a2 = thomp_contr inds p_bools e2 in
          let coprod_res = coprod a1 a2 in
          {
            states = coprod_res.states;
            inds;
            labels = Label.Set.union a1.labels a2.labels;
            p_bools;
            p_start =
              (fun i at ->
                if satisfy i at eb then coprod_res.left_start i at
                else coprod_res.right_start i at);
            trans = coprod_res.trans;
            jumps = coprod_res.jump;
          }
      | While (eb, e) ->
          let a = thomp_contr inds p_bools e in
          let p_start =
            resolve_break
            @@ resolve_loop eb a.p_start (PBool.atoms_of p_bools)
                 (Ind.Set.elements inds)
          in
          {
            inds;
            p_bools;
            labels = a.labels;
            states = a.states;
            p_start;
            (* loop the transmap by connecting it with the current start*)
            trans = (fun s -> resolve_break @@ PState.uni_cont (a.trans s) p_start);
            jumps = (fun l -> PState.uni_cont (a.jumps l) p_start);
          }
      | Break ->
          {
            inds;
            p_bools;
            labels = Label.Set.empty;
            states = State.Set.empty;
            p_start = (fun i _ -> Brk i);
            (* transiton don't matter since we have a empty state set *)
            trans = (fun _ _ _ -> Reject);
            jumps = (fun _ _ _ -> Reject);
          }
      | Return ->
          {
            inds;
            p_bools;
            labels = Label.Set.empty;
            states = State.Set.empty;
            p_start = (fun _ _ -> Ret);
            (* transiton don't matter since we have a empty state set *)
            trans = (fun _ _ _ -> Reject);
            jumps = (fun _ _ _ -> Reject);
          }
      | Goto l ->
          {
            inds;
            p_bools;
            labels = Label.Set.empty;
            states = State.Set.empty;
            p_start = (fun _ _ -> Goto l);
            (* transiton don't matter since we have a empty state set *)
            trans = (fun _ _ _ -> Reject);
            jumps = (fun _ _ _ -> Reject);
          }
      | Label l ->
          {
            inds;
            p_bools;
            labels = Label.Set.singleton l;
            states = State.Set.empty;
            p_start = (fun i _ -> Acc i);
            (* transiton don't matter since we have a empty state set *)
            trans = (fun _ _ _ -> Reject);
            jumps = (fun l' i _ -> if l = l' then Acc i else Reject);
          }
  end

  module Eq = struct
    module ToIntAut = ToAutomatonWith (State.MakePosInt)
    (** Converting to int automaton when checking equalites*)

    module ResGKATState = ToIntAut.AutomatonPStart.ResGKATState
    (** Result state of converting a CF-GKAT automaton with int state to GKAT automaton*)

    (** Indicator agnostic equivalence 
      
    This function is not used for decompilation verification, mainly for testing*)
    let equiv (e1 : t) (e2 : t) : bool =
      let ind_set = Ind.Set.union (inds_of e1) (inds_of e2) in
      (* add a new ind to the list,
         as it might have different behavior than indicators appeared in the expressions*)
      let inds = Ind.Set.add (Ind.fresh ind_set) ind_set in
      let p_bools = PBool.Set.union (p_bools_of e1) (p_bools_of e2) in
      let automaton1 = ToIntAut.thomp_contr inds p_bools e1 in
      (* print_endline
           ("CF-GKAT automaton 1: " ^ ToIntAut.AutomatonPStart.pprint automaton1);
         print_endline
           ("converted automaton 1: "
           ^ ToIntAut.AutomatonPStart.ResGKATAut.pprint
               (ToIntAut.AutomatonPStart.to_GKAT_automaton (Ind.fresh ind_set)
                  automaton1)); *)
      let automaton2 = ToIntAut.thomp_contr inds p_bools e2 in
      (* print_endline
           ("CF-GKAT automaton 2: " ^ ToIntAut.AutomatonPStart.pprint automaton2);
         print_endline
           ("converted automaton 2: "
           ^ ToIntAut.AutomatonPStart.ResGKATAut.pprint
               (ToIntAut.AutomatonPStart.to_GKAT_automaton (Ind.fresh ind_set)
                  automaton2)); *)
      (* equivalence over the resulting state type of GKAT automaton *)
      let module ResGKATAutoEq =
        GKAT.Automaton.Eq (ResGKATState) (ResGKATState) (PBool)
      in
      Ind.Set.for_all
        (fun start_i ->
          ResGKATAutoEq.equiv
            (ToIntAut.AutomatonPStart.to_GKAT_automaton start_i automaton1)
            (ToIntAut.AutomatonPStart.to_GKAT_automaton start_i automaton2))
        inds
  end

  module EqGKATWith (InpGKATState : State.S) = struct
    module InpGKATAut = GKAT.Automaton.Make (InpGKATState) (PBool)

    module ToIntAut = ToAutomatonWith (State.MakePosInt)
    (** Converting to int automaton when checking equalites*)

    module ResGKATState = ToIntAut.AutomatonPStart.ResGKATState
    (** Result state of converting a CF-GKAT automaton with int state to GKAT automaton*)

    (** Indicator agnostic equivalence between CF-GKAT expression and GKAT automaton
      
    This is used for decompilation verfication,
    where the GKAT automata represents unstructured low-level program,
    and the CF-GKAT expression represents the resulting high-level of the dempilation*)
    let eq ?(bench = false) (gkat_a : InpGKATAut.t) (e : t) =
      let start = Unix.gettimeofday () in
      let ind_set = inds_of e in
      let e_p_bools = p_bools_of e in
      if not @@ PBool.Set.subset e_p_bools gkat_a.p_bools then
        failwith
          "expression contains more primitive tests than the automaton, cannot \
           compare"
      else
        let p_bools = gkat_a.p_bools in
        (* add a new ind to the list,
           as it might have different behavior than indicators appeared in the expressions*)
        let inds = Ind.Set.add (Ind.fresh ind_set) ind_set in
        let after_collection = Unix.gettimeofday () in
        if bench then
          print_endline
            ("collecting info took "
            ^ (after_collection -. start |> string_of_float)
            ^ "seconds");
        let a_p_start = ToIntAut.thomp_contr inds p_bools e in
        let after_thomp = Unix.gettimeofday () in
        if bench then (
          print_endline
            ("thompson construction took "
            ^ (after_thomp -. after_collection |> string_of_float)
            ^ "seconds");
          print_endline
            ("Number of States in thompson's automaton: "
            ^ string_of_int (ToIntAut.State.Set.cardinal a_p_start.states));
          print_endline
            ("Number of indicators in thompson's automaton: "
            ^ string_of_int (Ind.Set.cardinal a_p_start.inds)));
        let module GKATAutomatonEq =
          GKAT.Automaton.Eq (InpGKATState) (ResGKATState) (PBool)
        in
        let res =
          match e with
          | Seq (IndAssign i, _) ->
              (* hack: if the expression starts with a indicator assignment to `i`,
                 then we only need to check equivalence with starting indicator as `i`*)
              GKATAutomatonEq.equiv gkat_a
                (ToIntAut.AutomatonPStart.to_GKAT_automaton i a_p_start)
          | _ ->
              Ind.Set.for_all
                (fun start_i ->
                  GKATAutomatonEq.equiv gkat_a
                    (ToIntAut.AutomatonPStart.to_GKAT_automaton start_i
                       a_p_start))
                inds
        in
        let after_equiv = Unix.gettimeofday () in
        if bench then
          print_endline
            ("equiv took "
            ^ (after_equiv -. after_thomp |> string_of_float)
            ^ " seconds\n");
        res
  end
end
