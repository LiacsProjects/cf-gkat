open Frontc
open Cabs
open Cprint

open KAT_Decompile
open Common.Structures
open Common.Modules

module IntInd = Ind.MakePosInt
module StringPBool = PBool.MakeString
module TestExp = CFGKAT.ExpOver (IntInd) (StringPBool)
module StringSet = Set.Make (String)

open TestExp

exception Expression_Not_Implemented of expression
exception Statement_Not_Implemented of statement
exception Expression_Not_Collectible of expression
exception Statement_Not_Prunable of statement

let files: string list ref = ref []

(* Options scanning *)
let opts = []

(* 
  type bExp =
    | PBool of PBool.t
    | Zero
    | One
    | IndEq of Ind.t
    | Or of bExp * bExp
    | And of bExp * bExp
    | Not of bExp
*)

let rec convert_expression e ind = match e, ind with
    BINARY (OR, eleft, eright), _ -> Or (convert_expression eleft ind, convert_expression eright ind)
  | BINARY (AND, eleft, eright), _ -> And (convert_expression eleft ind, convert_expression eright ind)
  | BINARY (EQ, VARIABLE n, CONSTANT (CONST_INT i)), Some iname -> if n = iname then IndEq (IntInd.of_int (int_of_string i)) else raise (Expression_Not_Implemented e)
  | BINARY (EQ, _, _), Some _ -> raise (Expression_Not_Implemented e)
  | BINARY (EQ, _, _), None -> raise (Expression_Not_Implemented e)
  | BINARY (NE, eleft, eright), _ -> Not (convert_expression (BINARY (EQ, eleft, eright)) ind)
  | UNARY (NOT, e), _ -> Not (convert_expression e ind)
  (* FIXME Check that the variable is indeed a PBool *)
  | CALL (VARIABLE n, _), _ -> PBool (StringPBool.of_string n)
  | _ -> raise (Expression_Not_Implemented e)
(*
    NOTHING
  (** Null-expression. Useful for return with no value or table
      declaration without size. *)
  | UNARY of unary_operator * expression
  (** Unary operator use. *)
  | BINARY of binary_operator * expression * expression
  (** Binary operator use. *)
  | QUESTION of expression * expression * expression
  (** "condition ? then-expression : else-expression" operator. *)
  | CAST of base_type * expression
  (** "(type)expresson" type casting. *)
  | CALL of expression * expression list
  (** Function call. *)
  | COMMA of expression list
  (** Sequence of expression separated with ",". *)
  | CONSTANT of constant
  (** Constant value. *)
  | VARIABLE of string
  (** Access to an identifier. *)
  | EXPR_SIZEOF of expression
  (** "sizeof" with expression. *)
  | TYPE_SIZEOF of base_type
  (** "sizeof" with type. *)
  | INDEX of expression * expression
  (** Access to an array item; *)
  | MEMBEROF of expression * string
  (** Indirection through ".". *)
  | MEMBEROFPTR of expression * string
  (** Pointer indirection through "->". *)
  | GNU_BODY of body
  (** GNU braces inside an expression. *)
  | DESIGNATED of string * expression
  (** Designated initialization, in compound constants only. *)
  | EXPR_LINE of expression * string * int
  (** Record the file and line of the expression. *)
*)

(*
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
*)

let rec fixup_conditional_exp e = match e with
    VARIABLE vname -> BINARY (NE, VARIABLE vname, CONSTANT (CONST_INT "0"))
  | BINARY (AND, eleft, eright) -> BINARY (AND, fixup_conditional_exp eleft, fixup_conditional_exp eright)
  | BINARY (OR, eleft, eright) -> BINARY (OR, fixup_conditional_exp eleft, fixup_conditional_exp eright)
  | _ -> e

let rec convert_statement st ind primitives = match st, ind with
    NOP, _ -> Test One
  | SEQUENCE (sta, stb), _ -> Seq (convert_statement sta ind primitives, convert_statement stb ind primitives)
  | BLOCK (_, b), _ -> convert_statement b ind primitives
  | BREAK, _ -> Break
  | RETURN _, _ -> Return
  | IF (e, stt, stf), _ -> If (convert_expression (fixup_conditional_exp e) ind, convert_statement stt ind primitives, convert_statement stf ind primitives)
  | WHILE (e, stw), _ -> While (convert_expression (fixup_conditional_exp e) ind, convert_statement stw ind primitives)
  | COMPUTATION (BINARY (ASSIGN, (VARIABLE vname), CONSTANT (CONST_INT i))), Some iname -> if vname = iname then IndAssign (IntInd.of_int (int_of_string i)) else raise (Statement_Not_Implemented st)
  |  COMPUTATION (BINARY (ASSIGN, (VARIABLE _), _)), Some _ -> raise (Statement_Not_Implemented st)
  |  COMPUTATION (BINARY (ASSIGN, (VARIABLE _), _)), None -> raise (Statement_Not_Implemented st)
  (* FIXME Check that it's indeed a PAct *)
  | COMPUTATION (CALL (VARIABLE n, _)), _ -> PAct (PAct.of_string n)
  (* FIXME is this  correct? *)
  | LABEL (l, st), _ -> Seq (Label (Label.of_string l), convert_statement st ind primitives)
  | GOTO l, _ -> Goto (Label.of_string l)
  | _ -> raise (Statement_Not_Implemented st)
 (* 
  | DOWHILE of expression * statement
  (** "do ... while" statement *)
  | FOR of expression * expression * expression * statement
  (** "for" statement. *)
  | CONTINUE
  (** "continue" statement. *)
  | SWITCH of expression * statement
  (** "switch" statement. Cases are put in the sub-statement as labels. *)
  | CASE of expression * statement
  (** "case" statement as a label. *)
  | DEFAULT of statement
  (** "default" statement as a label. *)
  | ASM of string
  (** Classical "asm" support. *)
  | GNU_ASM of string * gnu_asm_arg list * gnu_asm_arg list * string list
  (** GNU "asm" support. *)
  | STAT_LINE of statement * string * int
  (** Information the filename and the line number of the contained statement. *) *)

let rec variables_in ex = match ex with
    NOTHING -> StringSet.empty
  | UNARY (_, e) -> variables_in e
  | BINARY (_, eleft, eright) -> StringSet.union (variables_in eleft) (variables_in eright)
  | QUESTION (e, etrue, efalse) -> StringSet.union (StringSet.union (variables_in e) (variables_in etrue)) (variables_in efalse)
  | CAST (_, e) -> variables_in e
  | CALL (e, elist) -> List.fold_left (fun s e -> StringSet.union s (variables_in e)) (variables_in e) elist
  | COMMA elist -> List.fold_left (fun s e -> StringSet.union s (variables_in e)) StringSet.empty elist
  | CONSTANT _ -> StringSet.empty
  | VARIABLE v -> StringSet.singleton v
  | EXPR_SIZEOF e -> variables_in e
  | TYPE_SIZEOF _ -> StringSet.empty
  | INDEX (earray, emember) -> StringSet.union (variables_in earray) (variables_in emember)
  | MEMBEROF (e, _) -> variables_in e
  | MEMBEROFPTR (e, _) -> variables_in e
  (* FIXME reroute to some entry point for statements *)
  | GNU_BODY _ -> raise (Expression_Not_Collectible ex)
  | DESIGNATED (_, e) -> variables_in e
  | EXPR_LINE (e, _, _) -> variables_in e
  
let filter_constant_initialization (n, _, _, e) = match e with
    CONSTANT (CONST_INT _) -> Some n
  | NOTHING -> Some n
  | _ -> None
  
let find_indicator_candidates defs = StringSet.of_list (List.concat (List.map (fun d -> match d with DECDEF (_, _, nlst) ->  List.filter_map filter_constant_initialization nlst | _ -> []) defs))
    
let rec prune_indicator_candidates candidates body = match body with
    NOP -> candidates
  | COMPUTATION (BINARY (ASSIGN, (VARIABLE _), CONSTANT (CONST_INT _))) -> candidates
  | COMPUTATION (BINARY (EQ, (VARIABLE _), CONSTANT (CONST_INT _))) -> candidates
  | COMPUTATION (BINARY (NE, (VARIABLE _), CONSTANT (CONST_INT _))) -> candidates
  | COMPUTATION (BINARY (AND, eleft, eright)) -> prune_indicator_candidates (prune_indicator_candidates candidates (COMPUTATION eleft)) (COMPUTATION eright)
  | COMPUTATION (BINARY (OR, eleft, eright)) -> prune_indicator_candidates (prune_indicator_candidates candidates (COMPUTATION eleft)) (COMPUTATION eright)
  | COMPUTATION (VARIABLE _) -> candidates
  | COMPUTATION ex -> StringSet.diff candidates (variables_in ex)
  (* FIXME The definitions ignored here should be considered in the find_indicator_candidates function *)
  | BLOCK (_, body) -> prune_indicator_candidates candidates body
  | SEQUENCE (bodyleft, bodyright) -> prune_indicator_candidates (prune_indicator_candidates candidates bodyleft) bodyright
  | IF (e, strue, sfalse) -> prune_indicator_candidates (prune_indicator_candidates (prune_indicator_candidates candidates (COMPUTATION e)) strue) sfalse
  | WHILE (e, st) -> prune_indicator_candidates (prune_indicator_candidates candidates (COMPUTATION e)) st
  | DOWHILE (e, st) -> prune_indicator_candidates (prune_indicator_candidates candidates (COMPUTATION e)) st
  | BREAK -> candidates
  | CONTINUE -> candidates
  (* FIXME Interesting case: what if we find return (x == 0) where x is an indicator candidate? *)
  | RETURN e -> StringSet.diff candidates (variables_in e)
  | FOR (einit, etest, einc, st) -> prune_indicator_candidates (prune_indicator_candidates (prune_indicator_candidates (prune_indicator_candidates candidates (COMPUTATION einit)) (COMPUTATION etest)) (COMPUTATION einc)) st
  | SWITCH (e, st) -> prune_indicator_candidates (prune_indicator_candidates candidates (COMPUTATION e)) st
  | CASE (e, st) -> prune_indicator_candidates (prune_indicator_candidates candidates (COMPUTATION e)) st
  | DEFAULT st -> prune_indicator_candidates candidates st
  | LABEL (_, st) -> prune_indicator_candidates candidates st
  | GOTO _ -> candidates
  | ASM _ -> raise (Statement_Not_Prunable body)
  | GNU_ASM _ -> raise (Statement_Not_Prunable body)
  (* FIXME Find out what this is
  | STAT_LINE of statement * string * int
  (** Information the filename and the line number of the contained statement. *)*)
  | _ -> raise (Statement_Not_Prunable body)

(* TODO Implement *)
let collect_primitives _ = (StringSet.empty, StringSet.empty)
    (*DECDEF (VOID, _, nlst) -> List.iter (fun (n, _, _, _) -> Hashtbl.add (fst res) n (Hashtbl.length (fst res))) nlst
  | DECDEF (BOOL, _, nlst) -> List.iter (fun (n, _, _, _) -> Hashtbl.add (fst res) n (Hashtbl.length (snd res))) nlst
    *)

let convert_cdef cdef pbs = match cdef with
    FUNDEF ((_, _, (fname, _, _, _)), (defs, tempeh)) -> print_endline (String.concat " " ["Processing";  fname]);
      (try let indicators = prune_indicator_candidates (find_indicator_candidates defs) tempeh in
        let indicator = if StringSet.is_empty indicators then  let _ = print_endline "No indicator found" in None
        else let _ = print_endline (String.concat " " ["Indicator is"; StringSet.choose indicators]) in Some (StringSet.choose indicators) in
        print_endline (TestExp.pprint (convert_statement tempeh indicator pbs)) with
      | Expression_Not_Implemented e -> print_endline "Expression not implemented:"; print_expression e 0; Cprint.force_new_line ()
      | Statement_Not_Implemented s -> print_endline "Statement not implemented:"; print_statement s
      | Expression_Not_Collectible e -> print_endline "Cannot collect variables in expression"; print_expression e 0; Cprint.force_new_line ()
      | Statement_Not_Prunable s -> print_endline "Cannot prune variables in statement"; print_statement s)
  | _ -> print_endline "Ignoring definition that is not a function"

(* Main Program *)
let () =
  (* Parse arguments *)
  Arg.parse opts (fun file -> files := file :: !files) "Missing file";

  (* Process the input *)
  let process opts =
    match Frontc.parse opts with
      PARSING_ERROR ->  ()
    | PARSING_OK file -> let pbs = collect_primitives file in List.iter (fun cdef -> convert_cdef cdef pbs) file
    in
  (* Process the inputs *)
  List.iter (fun file -> process [FROM_FILE file]) !files
