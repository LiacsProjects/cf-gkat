open Clang2CFGKAT
open Clang
open Clang.Ast

module StringSet = Set.Make (String)

module StringHashtbl = Hashtbl.Make (struct
  type t = string
  let equal = String.equal
  let hash = Hashtbl.hash
end)

let usage_msg = "blinder <file>"

let clang_opts = ref ""

let input_files = ref []

let primitives = ref (StringHashtbl.create 0)

type ptype = PrimBool | PrimAct

let output_primitive (p : ptype) (key : string) : string =
    let b = if (StringHashtbl.mem !primitives key) then (StringHashtbl.find !primitives key) else (let value = StringHashtbl.length !primitives in let _ = StringHashtbl.add !primitives key value in value) in
    (match p with PrimBool -> "pbool" | PrimAct -> "pact") ^ "(" ^ (string_of_int b) ^ ")" ^ (match p with PrimBool -> "" | PrimAct -> ";\n")
  
let rec blinded_expr (ind : string option) : expr -> string = function
    (* NOTE There is a constructor IntegerLiteral (CXInt _) which should be admitted *)
    { desc=(BinaryOperator { lhs=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }); kind=EQ; rhs=({ desc=(IntegerLiteral (Int _)); decoration=_ }) }); decoration=_ } as m -> (match ind with
      None -> output_primitive PrimBool (node_str m)
    | Some i -> if n = i then (node_str m) else  output_primitive PrimBool (node_str m)
  )
  (* NOTE Maybe we could skip the declaration altogether since it will not matter *)
  | { desc=(BinaryOperator { lhs=({ desc=(DeclRef { name=(IdentifierName _); _ }); decoration=_ }); kind=EQ; rhs=_ }); decoration=_ } as n -> output_primitive PrimBool (node_str n)
  | { desc=(BinaryOperator { lhs=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }); kind=NE; rhs=({ desc=(IntegerLiteral (Int _)); decoration=_ }) }); decoration=_ } as m -> (match ind with
      None ->  output_primitive PrimBool (node_str m)
    | Some i -> if n = i then (node_str m) else  output_primitive PrimBool (node_str m)
  )
  | { desc=(BinaryOperator { lhs=l; kind=LAnd; rhs=r }); decoration=_ } -> (blinded_expr ind l) ^ " && " ^ (blinded_expr ind r)
  | { desc=(BinaryOperator { lhs=l; kind=LOr; rhs=r }); decoration=_ } -> (blinded_expr ind l) ^ " || " ^ (blinded_expr ind r)
  | { desc=(BinaryOperator _); decoration=_ } as n ->  output_primitive PrimBool (node_str n)
  | { desc=(UnaryOperator { kind=LNot; operand=e }); decoration=_ } -> "!" ^ (blinded_expr ind e)
  | { desc=(UnaryOperator _); decoration=_ } as n -> output_primitive PrimBool (node_str n)
  | { desc=(Call { callee=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }); args=a }); decoration=_ } -> output_primitive PrimBool (function_str ind n a)
  | { desc=(Paren e); decoration=_ } -> "(" ^ (blinded_expr ind e) ^ ")"
  | { desc=(DeclRef { name=(IdentifierName _); _ }); decoration=_ } as n ->  output_primitive PrimBool (node_str n)
  | { desc=(Cast { kind=CStyle; qual_type=({ cxtype=t; _ }); operand=e }); decoration=_ } -> "(" ^ (get_type_spelling t) ^ ")" ^ (blinded_expr ind e)
  | { desc=(IntegerLiteral (Int i)); decoration=_ } -> string_of_int i
  | { desc=(Member { base=(Some { desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }); arrow=a; field=(FieldName { desc=({ name=(IdentifierName m); _ }); _ }) }); decoration=_ } -> output_primitive PrimBool (n ^ (if a then "->" else ".") ^ m)
  | { desc=(ArraySubscript { base=b; index=i }); decoration=_ } -> output_primitive PrimBool ((blinded_expr ind b) ^ "[" ^ (blinded_expr ind i) ^ "]")
  | e -> node_str e
and function_str ind fname args = fname ^ "(" ^ (String.concat ", " (List.map (blinded_expr ind) args)) ^ ")"
  
let decl_str_value ind : expr option -> string = function
    None -> ""
  | Some { desc=(IntegerLiteral (Int l)); decoration=_ } -> " = " ^ (string_of_int l)
  | Some e -> (blinded_expr ind e)

let decl_str ind : decl -> string = function
    { desc=(Var { var_name=v; var_type={ cxtype=vt; _ }; var_init=i; _ }); _ } -> let key = (get_type_spelling vt) ^ " " ^ v ^ (decl_str_value ind i) in
        (match get_type_kind vt with
            UShort | UInt | ULong | ULongLong | UInt128 | Short | Int | Long | LongLong | Int128 -> (match ind with
                None ->  output_primitive PrimAct key
              | Some i -> if v = i then key ^ ";\n" else output_primitive PrimAct key)
          | _ -> output_primitive PrimAct key)
  | d -> output_primitive PrimAct (node_str d)

let rec blinded_stmt (ind : string option) : stmt -> string = function 
    { desc=(Compound []); decoration=_ } -> ""
  | { desc=(Compound (x :: t)); decoration=d } -> (blinded_stmt ind x) ^ (blinded_stmt ind { desc=(Compound t); decoration=d })
  | { desc=(While { cond=e; body=b; _ }); decoration=_ } ->"while (" ^ (blinded_expr ind e) ^ ") {\n" ^ (blinded_stmt ind b) ^ "\n}\n"
  | { desc=(Do { body=b; cond=e }); decoration=_ } ->"do {\n" ^ (blinded_stmt ind b) ^ "\n} while (" ^ (blinded_expr ind e) ^ ");\n"
  | { desc=(For { init=None; cond=cond; inc=None; body=b; _ }); decoration=_ } -> "for (; " ^ (Option.fold ~none:"" ~some:(blinded_expr ind) cond) ^ ";) {\n" ^ (blinded_stmt ind b) ^ "\n}\n"
  | { desc=(For { init=None; cond=cond; inc=(Some { desc=(Expr inc); decoration=_ }); body=b; _ }); decoration=_ } -> "for (; " ^ (Option.fold ~none:"" ~some:(blinded_expr ind) cond) ^ "; " ^ (blinded_expr ind inc) ^ ") {\n" ^ (blinded_stmt ind b) ^ "\n}\n"
  | { desc=(For { init=(Some { desc=(Expr init); decoration=_ }); cond=cond; inc=None; body=b; _ }); decoration=_ } -> "for (" ^ (blinded_expr ind init) ^ "; " ^ (Option.fold ~none:"" ~some:(blinded_expr ind) cond) ^ ";) {\n" ^ (blinded_stmt ind b) ^ "\n}\n"
  | { desc=(For { init=(Some { desc=(Expr init); decoration=_ }); cond=cond; inc=(Some { desc=(Expr inc); decoration=_ }); body=b; _ }); decoration=_ } -> "for (" ^ (blinded_expr ind init) ^ "; " ^ (Option.fold ~none:"" ~some:(blinded_expr ind) cond) ^ "; " ^ (blinded_expr ind inc) ^ ") {\n" ^ (blinded_stmt ind b) ^ "\n}\n"
  | { desc=(For { init=(Some ({ desc=(Decl (_ :: [])); decoration=_ } as init)); cond=cond; inc=(Some { desc=(Expr inc); decoration=_ }); body=b; _ }); decoration=_ } -> "for (" ^ (blinded_stmt ind init) ^ (Option.fold ~none:"" ~some:(blinded_expr ind) cond) ^ "; " ^ (blinded_expr ind inc) ^ ") {\n" ^ (blinded_stmt ind b) ^ "\n}\n"
  | { desc=(For { init=(Some ({ desc=(Decl (_ :: [])); decoration=_ } as init)); cond=cond; inc=None; body=b; _ }); decoration=_ } -> "for (" ^ (blinded_stmt ind init) ^ (Option.fold ~none:"" ~some:(blinded_expr ind) cond) ^ ";) {\n" ^ (blinded_stmt ind b) ^ "\n}\n"
  | { desc=(If { cond=e; then_branch=then_stmt; else_branch=None; _ }); decoration=_ } -> "if (" ^ (blinded_expr ind e) ^ ") {\n" ^ (blinded_stmt ind then_stmt) ^ "\n}\n"
  | { desc=(If { cond=e; then_branch=then_stmt; else_branch=(Some else_stmt); _ }); decoration=_ } -> "if (" ^ (blinded_expr ind e) ^ ") {\n" ^ (blinded_stmt ind then_stmt) ^ "\n} else {\n" ^ (blinded_stmt ind else_stmt) ^ "\n}\n"
  | { desc=(Decl dlist); decoration=_ } -> String.concat "\n" (List.map (decl_str ind) dlist)
  | { desc=(Return (Some e)); decoration=_ } -> "return " ^ (output_primitive PrimBool (blinded_expr ind e)) ^ ";\n"
  | { desc=(Label { label=l; body=b }); decoration=_ } -> l ^ ": " ^ (blinded_stmt ind b)
  | { desc=(Expr { desc=(Call { callee=({ desc=(DeclRef { name=(IdentifierName "assert"); _ }); _ }); args=a }); decoration=_ }); decoration=_ } ->  (function_str ind "assert" a) ^ ";\n"
  | { desc=(Expr { desc=(Call { callee=({ desc=(DeclRef { name=(IdentifierName n); _ }); _ }); args=a }); decoration=_ }); decoration=_ } ->  output_primitive PrimAct (function_str ind n a)
    (* NOTE There is a constructor IntegerLiteral (CXInt _) which should be admitted *)
  | { desc=(Expr { desc=(BinaryOperator { lhs=({ desc=(DeclRef { name=(IdentifierName n); _ }); decoration=_ }); kind=Assign; rhs=({ desc=(IntegerLiteral (Int _)); decoration=_ }) }); decoration=_ }); decoration=_ } as vnode -> (match ind with
      None -> output_primitive PrimAct (node_str vnode) ^ ";\n"
    | Some i -> if n = i then (node_str vnode) else output_primitive PrimAct (node_str vnode)
  )
  | { desc=(Expr _); decoration=_ } as n-> output_primitive PrimAct (node_str n)
  | { desc=(Null); decoration=_ } -> ""
  | s -> (node_str s) ^ ";\n"

(* FIXME This indicator detection dance should be abstracted somewhere *)
let blind_function fname : decl_desc node -> unit = function
    { desc=(Function { name=(IdentifierName n); body=(Some b); function_type=({ result=({ cxtype=t; _ }); _ }); _ }); decoration=_ } -> (try (
      let vi = valid_invalid_indicators b in
      let ind = StringSet.choose_opt (StringSet.diff (fst vi) (snd vi)) in
      let _ = (match ind with Some v -> Printf.eprintf "blinder - %s,%s,1,%s\n%!" fname n v | None -> Printf.eprintf "blinder - %s,%s,1,\n%!" fname n) in
      print_endline ((match get_type_kind t with Void -> "void" | _ -> "_Bool") ^ " " ^ n ^ "() {");
      print_endline (blinded_stmt ind b);
      print_endline "}") with
        _ -> Printf.eprintf "blinder - %s,%s,0,\n%!" fname n)
  | _ -> ()

let is_local f : decl_desc node -> bool = function
    { desc=_; decoration=d } -> let l = location_of_decoration d in match l with Concrete { filename=g; _ } -> f = g | Clang cxl -> (match get_presumed_location cxl with (g, _, _) -> f = g)

let () =
    Arg.parse [("--clang", Arg.Set_string clang_opts, "Pass option string to Clang")] (fun filename -> input_files := filename :: !input_files) usage_msg;;
    let idx = create_index ~exclude_declarations_from_pch:true ~display_diagnostics:true;;
    let file = List.hd !input_files in
    match Clang.Ast.parse_file ~index:idx ~command_line_args:(String.split_on_char ' ' !clang_opts) ~unsaved_files:[] ~options:Ast.Options.default file with
        { desc={ filename=f; items=i }; decoration=_ } ->
(*           Printf.eprintf "%s\n%!" f; *)
          print_endline "void assert(_Bool x);";
          print_endline "_Bool pbool(int);\n";
          print_endline "void pact(int);\n";
          List.iter (blind_function f) (List.filter (is_local f) i)
