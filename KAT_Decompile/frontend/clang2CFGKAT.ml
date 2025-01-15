open Clang
open Clang.Ast

open KAT_Decompile
open Common.Structures
open Common.Modules

module IntInd = Ind.MakePosInt
module StringPBool = PBool.MakeString
module CFGKATExp = CFGKAT.ExpOver (IntInd) (StringPBool)
module StringSet = Set.Make (String)

open CFGKATExp

let pointwise f a b = (f (fst a) (fst b), f (snd a) (snd b))

let node_str n = (String.concat " " (Array.to_list (tokens_of_node n)))
  
let string_of_args args = String.concat "," (List.map node_str args)

let rec convert_expr (ind : string option) : expr -> bExp = function
    (* NOTE There is a constructor IntegerLiteral (CXInt _) which should be admitted *)
    { desc=(BinaryOperator { lhs=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }); kind=EQ; rhs=({ desc=(IntegerLiteral (Int l)); decoration=_ }) }); decoration=_ } -> (match ind with
      None -> PBool (StringPBool.of_string (n ^ " == " ^ (string_of_int l)))
    | Some i -> if n = i then IndEq (IntInd.of_int l) else PBool (StringPBool.of_string (n ^ " == " ^ (string_of_int l)))
  )
  | { desc=(BinaryOperator { lhs=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }); kind=EQ; rhs=_ }); decoration=_ } -> PBool (StringPBool.of_string (n ^ " = ..."))
  | { desc=(BinaryOperator { lhs=l; kind=NE; rhs=r }); decoration=d } -> Not (convert_expr ind { desc=(BinaryOperator { lhs=l; kind=EQ; rhs=r }); decoration=d })
  | { desc=(BinaryOperator { lhs=l; kind=LAnd; rhs=r }); decoration=_ } -> And (convert_expr ind l, convert_expr ind r)
  | { desc=(BinaryOperator { lhs=l; kind=LOr; rhs=r }); decoration=_ } -> Or (convert_expr ind l, convert_expr ind r)
  | { desc=(BinaryOperator _); decoration=_ } as n -> PBool (StringPBool.of_string (node_str n))
  | { desc=(UnaryOperator { kind=LNot; operand=e }); decoration=_ } -> Not (convert_expr ind e)
  | { desc=(Call { callee=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }); args=({ desc=(IntegerLiteral (Int l)); decoration=_ }::[]) }); decoration=_ } -> PBool (StringPBool.of_string (n ^ "(" ^ (string_of_int l) ^ ")"))
  | { desc=(Call { callee=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }); args=a }); decoration=_ } -> PBool (StringPBool.of_string (n ^ "(" ^ (string_of_args a) ^ ")"))
  | { desc=(Paren e); decoration=_ } -> convert_expr ind e
  | { desc=(IntegerLiteral (Int l)); decoration=_ } -> if l = 0 then Zero else One
  | { desc=(BoolLiteral b); decoration=_ } -> if b then One else Zero
  | { desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ } -> PBool (StringPBool.of_string n)
  | { desc=(Cast { operand=o; _ }); decoration=_ } -> convert_expr ind o
  | e -> failwith ("Expr not supported" ^ (node_str e))

let rec convert_stmt (ind : string option) : stmt -> CFGKATExp.t = function 
    { desc=(Compound []); decoration=_ } -> Test One
  | { desc=(Compound (x :: t)); decoration=d } -> Seq (convert_stmt ind x, convert_stmt ind { desc=(Compound t); decoration=d })
  | { desc=(While { cond=e; body=b; _ }); decoration=_ } -> While (convert_expr ind e, convert_stmt ind b)
  | { desc=(Do { body=b; cond=e; }); decoration=_ } -> let bst = convert_stmt ind b in Seq (bst, While (convert_expr ind e, bst))
  | { desc=(For { init=None; cond=None; inc=None; body=b; _ }); decoration=_ } -> While (One, convert_stmt ind b)
  | { desc=(For { init=(Some fa); cond=None; inc=None; body=b; _ }); decoration=_ } -> Seq (convert_stmt ind fa, While (One, convert_stmt ind b))
  | { desc=(For { init=None; cond=(Some fb); inc=None; body=b; _ }); decoration=_ } -> While (convert_expr ind fb, convert_stmt ind b)
  | { desc=(For { init=None; cond=None; inc=(Some fc); body=b; _ }); decoration=_ } -> While (One, Seq (convert_stmt ind b, convert_stmt ind fc))
  | { desc=(For { init=(Some fa); cond=(Some fb); inc=None; body=b; _ }); decoration=_ } -> Seq (convert_stmt ind fa, While (convert_expr ind fb, convert_stmt ind b))
  | { desc=(For { init=(Some fa); cond=None; inc=(Some fc); body=b; _ }); decoration=_ } -> Seq (convert_stmt ind fa, While (One, Seq (convert_stmt ind b, convert_stmt ind fc)))
  | { desc=(For { init=None; cond=(Some fb); inc=(Some fc); body=b; _ }); decoration=_ } -> While (convert_expr ind fb, Seq (convert_stmt ind b, convert_stmt ind fc))
  | { desc=(For { init=(Some fa); cond=(Some fb); inc=(Some fc); body=b; _ }); decoration=_ } -> Seq (convert_stmt ind fa, While (convert_expr ind fb, Seq (convert_stmt ind b, convert_stmt ind fc)))
  | { desc=(If { cond=e; then_branch=then_stmt; else_branch=None; _ }); decoration=_ } -> If (convert_expr ind e, convert_stmt ind then_stmt, Test One)
  | { desc=(If { cond=e; then_branch=then_stmt; else_branch=(Some else_stmt); _ }); decoration=_ } -> If (convert_expr ind e, convert_stmt ind then_stmt, convert_stmt ind else_stmt)
  | { desc=(Decl []); decoration=_ } -> Test One
  | { desc=(Decl ({ desc=(Var { var_name=v; var_type={ cxtype=vt; _ }; var_init=None; _ }); _ } :: t)); decoration=d } -> let sthead = (match get_type_kind vt with
      UShort | UInt | ULong | ULongLong | UInt128 | Short | Int | Long | LongLong | Int128 -> (match ind with
          None -> PAct (PAct.of_string v)
        | Some i -> if v = i then Test One else PAct (PAct.of_string v))
    | _ -> PAct (PAct.of_string v)
  ) in let sttail = convert_stmt ind { desc=(Decl t); decoration=d } in Seq (sthead, sttail)
    (* NOTE There is a constructor IntegerLiteral (CXInt _) which should be admitted *)
  | { desc=(Decl ({ desc=(Var { var_name=v; var_type={ cxtype=vt; _ }; var_init=(Some ({ desc=(IntegerLiteral (Int l)); decoration=_ })); _ }); _ } :: t)); decoration=d } -> let sthead = (match get_type_kind vt with
      UShort | UInt | ULong | ULongLong | UInt128 | Short | Int | Long | LongLong | Int128 -> (match ind with
          None-> PAct (PAct.of_string (v ^ " = " ^ (string_of_int l)))
        | Some i -> if v = i then IndAssign (IntInd.of_int l) else PAct (PAct.of_string (v ^ " = " ^ (string_of_int l))))
    | _ -> PAct (PAct.of_string (v ^ " = " ^ (string_of_int l)))
  ) in let sttail = convert_stmt ind { desc=(Decl t); decoration=d } in Seq (sthead, sttail)
  | { desc=(Decl (h :: t)); decoration=d } -> let sttail = convert_stmt ind { desc=(Decl t); decoration=d } in Seq (PAct (PAct.of_string (node_str h)), sttail)
  | { desc=(Return None); decoration=_ } -> Return
  | { desc=(Return (Some e)); decoration=_ } -> Seq (PAct (PAct.of_string (node_str e)), Return)
  | { desc=(Label { label=l; body=b }); decoration=_ } -> Seq (Label (Label.of_string l), convert_stmt ind b)
  | { desc=(Goto l); decoration=_ } -> Goto (Label.of_string l)
  | { desc=(Break); decoration=_ } -> Break;
  | { desc=(Expr { desc=(Call { callee=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }); args=a }); decoration=_ }); decoration=_ } -> if n = "assert" then Test (convert_expr ind (List.hd a)) else PAct (PAct.of_string (n ^ "(" ^ (match a with ({ desc=(IntegerLiteral (Int l)); decoration=_ })::[] -> string_of_int l | _ -> string_of_args a) ^ ")"))
    (* NOTE There is a constructor IntegerLiteral (CXInt _) which should be admitted *)
  | { desc=(Expr { desc=(BinaryOperator { lhs=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }); kind=Assign; rhs=({ desc=(IntegerLiteral (Int l)); decoration=_ }) }); decoration=_ }); decoration=_ } -> (match ind with
      None -> PAct (PAct.of_string (n ^ " = " ^ (string_of_int l)))
    | Some i -> if n = i then IndAssign (IntInd.of_int l) else PAct (PAct.of_string (n ^ " = " ^ (string_of_int l)))
  )
  | { desc=(Expr { desc=(BinaryOperator { lhs=l; kind=Assign; rhs=r }); decoration=_ }); decoration=_ } -> PAct (PAct.of_string ((node_str l) ^ " = " ^ (node_str r)))
  | { desc=(Expr { desc=(BinaryOperator _); decoration=_ }); decoration=_ } as n -> PAct (PAct.of_string (node_str n))
  | { desc=(Expr { desc=(UnaryOperator { kind=PostInc; operand=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }) }); decoration=_ }); decoration=_ } -> PAct (PAct.of_string (n ^ "++"))
  | { desc=(Expr { desc=(UnaryOperator { kind=PostDec; operand=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }) }); decoration=_ }); decoration=_ } -> PAct (PAct.of_string (n ^ "--"))
  | { desc=(Expr { desc=(UnaryOperator { kind=PreInc; operand=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }) }); decoration=_ }); decoration=_ } -> PAct (PAct.of_string ("++" ^ n))
  | { desc=(Expr { desc=(UnaryOperator { kind=PreDec; operand=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }) }); decoration=_ }); decoration=_ } -> PAct (PAct.of_string ("--" ^ n))
  | { desc=(Expr { desc=(ConditionalOperator { cond=e; then_branch=None; else_branch=f; }); decoration=d }); decoration=_ } -> If (convert_expr ind e, convert_stmt ind { desc=(Expr e); decoration=d }, convert_stmt ind { desc=(Expr f); decoration=d })
  | { desc=(Expr { desc=(ConditionalOperator { cond=e; then_branch=(Some t); else_branch=f; }); decoration=d }); decoration=_ } -> If (convert_expr ind e, convert_stmt ind { desc=(Expr t); decoration=d }, convert_stmt ind { desc=(Expr f); decoration=d })
  | { desc=(Null); decoration=_ } -> Test One
  | s -> failwith ("Stmt not supported in " ^ (match location_of_node s with Concrete { line=l; column=c; filename=_ } -> (string_of_int l) ^ ":" ^ (string_of_int c) | Clang cxl -> (match get_presumed_location cxl with (f, l, c) -> f ^ ":" ^ (string_of_int l) ^ ":" ^ (string_of_int c))))

let filter_var : expr -> string option = function
    { desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ } -> Some n
  | _ -> None
  
let rec invalid_indicators : expr -> StringSet.t = function
    { desc=(BinaryOperator { lhs=({ desc=(DeclRef { name=(IdentifierName _); _ }); decoration=_ }); kind=EQ; rhs=({ desc=(IntegerLiteral _); decoration=_ }) }); decoration=_ } -> StringSet.empty
  | { desc=(BinaryOperator { lhs=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }); kind=EQ; rhs=_ }); decoration=_ } -> StringSet.singleton n
  | { desc=(BinaryOperator { lhs=l; kind=NE; rhs=r }); decoration=d } -> invalid_indicators { desc=(BinaryOperator { lhs=l; kind=EQ; rhs=r }); decoration=d }
  | { desc=(BinaryOperator { lhs=_; kind=EQ; rhs=_ }); decoration=_ } -> StringSet.empty
  | { desc=(BinaryOperator { lhs=l; kind=_; rhs=r }); decoration=_ } -> StringSet.union (invalid_indicators l) (invalid_indicators r)
  | { desc=(UnaryOperator { kind=_; operand=e }); decoration=_ } -> invalid_indicators e
  | { desc=(Call { callee=({ desc=(DeclRef { name=(IdentifierName _); _ }); decoration=_ }); args=a }); decoration=_ } -> StringSet.of_list (List.filter_map filter_var a)
  | { desc=(Paren e); decoration=_ } -> invalid_indicators e
  | { desc=(IntegerLiteral _); decoration=_ } -> StringSet.empty
  | { desc=(BoolLiteral _); decoration=_ } -> StringSet.empty
  | { desc=(StringLiteral _); decoration=_ } -> StringSet.empty
  | { desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ } -> StringSet.singleton n
  | { desc=(ArraySubscript { base=b; index=i }); decoration=_ } -> StringSet.union (invalid_indicators b) (invalid_indicators i)
  | { desc=(Cast { operand=e; _ }); decoration=_ } -> invalid_indicators e
  | { desc=(Member { base=(Some e); _ }); decoration=_ } -> invalid_indicators e
  | { desc=(UnaryExpr _); decoration=_ } -> StringSet.empty
  | e -> failwith ("Cannot find invalid indicators in " ^ (match location_of_node e with Concrete { line=l; column=c; filename=_ } -> (string_of_int l) ^ ":" ^ (string_of_int c) | Clang cxl -> (match get_presumed_location cxl with (f, l, c) -> f ^ ":" ^ (string_of_int l) ^ ":" ^ (string_of_int c))))
  
let rec valid_invalid_indicators : stmt -> StringSet.t * StringSet.t = function 
    { desc=(Compound []); decoration=_ } -> (StringSet.empty, StringSet.empty)
  | { desc=(Compound (x :: t)); decoration=d } -> let virest = valid_invalid_indicators { desc=(Compound t); decoration=d } in let vihead = valid_invalid_indicators x in (pointwise StringSet.union vihead virest)
  | { desc=(While { cond=e; body=b; _ }); decoration=_ } -> let inv = invalid_indicators e in let vibody = valid_invalid_indicators b in (fst vibody, StringSet.union inv (snd vibody))
  | { desc=(Do { body=b; cond=e }); decoration=_ } -> let inv = invalid_indicators e in let vibody = valid_invalid_indicators b in (fst vibody, StringSet.union inv (snd vibody))
  | { desc=(For { init=None; cond=None; inc=None; body=b; _ }); decoration=_ } -> valid_invalid_indicators b
  | { desc=(For { init=(Some fa); cond=None; inc=None; body=b; _ }); decoration=_ } -> pointwise StringSet.union (valid_invalid_indicators fa) (valid_invalid_indicators b)
  | { desc=(For { init=None; cond=(Some fb); inc=None; body=b; _ }); decoration=_ } -> let vi = valid_invalid_indicators b in (fst vi, StringSet.union (snd vi) (invalid_indicators fb))
  | { desc=(For { init=None; cond=None; inc=(Some fc); body=b; _ }); decoration=_ } -> pointwise StringSet.union (valid_invalid_indicators b) (valid_invalid_indicators fc)
  | { desc=(For { init=(Some fa); cond=(Some fb); inc=None; body=b; _ }); decoration=_ } -> let vi = pointwise StringSet.union (valid_invalid_indicators fa) (valid_invalid_indicators b) in (fst vi, StringSet.union (invalid_indicators fb) (snd vi))
  | { desc=(For { init=(Some fa); cond=None; inc=(Some fc); body=b; _ }); decoration=_ } -> pointwise StringSet.union (pointwise StringSet.union (valid_invalid_indicators fa) (valid_invalid_indicators b)) (valid_invalid_indicators fc)
  | { desc=(For { init=None; cond=(Some fb); inc=(Some fc); body=b; _ }); decoration=_ } -> let vi = pointwise StringSet.union (valid_invalid_indicators b) (valid_invalid_indicators fc) in (fst vi, StringSet.union (invalid_indicators fb) (snd vi))
  | { desc=(For { init=(Some fa); cond=(Some fb); inc=(Some fc); body=b; _ }); decoration=_ } -> let vi = pointwise StringSet.union (pointwise StringSet.union (valid_invalid_indicators fa) (valid_invalid_indicators b)) (valid_invalid_indicators fc) in (fst vi, StringSet.union (invalid_indicators fb) (snd vi))
  | { desc=(If { cond=e; then_branch=then_stmt; else_branch=None; _ }); decoration=_ } -> let inv = invalid_indicators e in let vithen = valid_invalid_indicators then_stmt in (fst vithen, StringSet.union inv (snd vithen))
  | { desc=(If { cond=e; then_branch=then_stmt; else_branch=(Some else_stmt); _ }); decoration=_ } -> let inv = invalid_indicators e in let vithen = valid_invalid_indicators then_stmt in let vielse = valid_invalid_indicators else_stmt in (pointwise StringSet.union (pointwise StringSet.union vithen vielse) (StringSet.empty, inv))
  | { desc=(Decl []); decoration=_ } -> (StringSet.empty, StringSet.empty)
  | { desc=(Decl ({ desc=(Var { var_name=v; var_type={ cxtype=vt; _ }; var_init=(None | Some ({ desc=(IntegerLiteral _); decoration=_ })); _ }); _ } :: t)); decoration=d } -> let vihead = (match get_type_kind vt with
      UShort | UInt | ULong | ULongLong | UInt128 | Short | Int | Long | LongLong | Int128 -> (StringSet.singleton v, StringSet.empty)
    | _ -> (StringSet.empty, StringSet.singleton v)
  ) in let vitail = valid_invalid_indicators { desc=(Decl t); decoration=d } in pointwise StringSet.union vihead vitail
  | { desc=(Decl ({ desc=(Var { var_name=v; var_init=(Some _); _ }); _ } :: t)); decoration=d } -> let vitail = valid_invalid_indicators { desc=(Decl t); decoration=d } in (fst vitail, StringSet.add v (snd vitail))
  | { desc=(Return (Some e)); decoration=_ } -> (StringSet.empty, invalid_indicators e)
  | { desc=(Return None); decoration=_ } -> (StringSet.empty, StringSet.empty)
  | { desc=(Label _); decoration=_ } -> (StringSet.empty, StringSet.empty)
  | { desc=(Goto _); decoration=_ } -> (StringSet.empty, StringSet.empty)
  | { desc=(Break); decoration=_ } -> (StringSet.empty, StringSet.empty)
  | { desc=(Expr { desc=(Call { callee=_; args=a }); decoration=_ }); decoration=_ } -> (StringSet.empty, StringSet.of_list (List.filter_map filter_var a))
  | { desc=(Expr { desc=(BinaryOperator { lhs=({ desc=(DeclRef { name=(IdentifierName _); _ }); decoration=_ }); kind=Assign; rhs=({ desc=(IntegerLiteral _); decoration=_ }) }); decoration=_ }); decoration=_ } -> (StringSet.empty, StringSet.empty)
  | { desc=(Expr { desc=(BinaryOperator { lhs=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }); kind=Assign; rhs=_ }); decoration=_ }); decoration=_ } -> (StringSet.empty, StringSet.singleton n)
  | { desc=(Expr { desc=(BinaryOperator { lhs=_; kind=Assign; rhs=_ }); decoration=_ }); decoration=_ } -> (StringSet.empty, StringSet.empty)
  | { desc=(Expr { desc=(UnaryOperator { kind=(PostInc | PostDec | PreInc | PreDec); operand=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }) }); decoration=_ }); decoration=_ } -> (StringSet.empty, StringSet.singleton n)
  | { desc=(Expr { desc=(ConditionalOperator { cond=e; then_branch=None; else_branch=f; }); decoration=d }); decoration=_ } -> let einv = valid_invalid_indicators { desc=(Expr e); decoration=d } in let finv = valid_invalid_indicators { desc=(Expr f); decoration=d } in pointwise StringSet.union einv finv
  | { desc=(Expr { desc=(ConditionalOperator { cond=e; then_branch=(Some t); else_branch=f; }); decoration=d }); decoration=_ } -> let einv = valid_invalid_indicators { desc=(Expr e); decoration=d } in let tinv = valid_invalid_indicators { desc=(Expr t); decoration=d } in let finv = valid_invalid_indicators { desc=(Expr f); decoration=d } in pointwise StringSet.union einv (pointwise StringSet.union tinv finv)
  | { desc=(Expr e); decoration=_ } -> (StringSet.empty, invalid_indicators e)
  | { desc=(Null); decoration=_ } -> (StringSet.empty, StringSet.empty)
  | { desc=(UnknownStmt _); decoration=_ } -> failwith "Unknown statement"
  | s -> failwith ("Cannot examine indicators in " ^ (match location_of_node s with Concrete { line=l; column=c; filename=_ } -> (string_of_int l) ^ ":" ^ (string_of_int c) | Clang cxl -> (match get_presumed_location cxl with (f, l, c) -> f ^ ":" ^ (string_of_int l) ^ ":" ^ (string_of_int c))))

type convres = ConvSuccess of CFGKATExp.t | ConvFailure of string
  
let convert_function : decl_desc node -> (string * convres) option = function
    { desc=(Function { name=(IdentifierName n); body=(Some b); _ }); decoration=_ } -> (try
        let vi = valid_invalid_indicators b in
        let ind = StringSet.choose_opt (StringSet.diff (fst vi) (snd vi)) in
        let _ = (match ind with Some v -> print_endline ("Indicator is " ^ v) | None -> print_endline "No indicator") in
        Some (n, ConvSuccess (convert_stmt ind b)) with
            Failure e -> Some (n, ConvFailure e))
  | _ -> None
