open Clang2CFGKAT
open Clang
open Clang.Ast

module StringSet = Set.Make (String)

let usage_msg = "convertfun <file> [<fun> ...]"

let clang_opts = ref ""

let input_files = ref []

let decl_in_function_set s : decl_desc node -> bool = function
    { desc=(Function { name=(IdentifierName n); _ }); decoration=_ } -> StringSet.mem n s
  | _ -> false

let rec functions_and_file s : string list -> StringSet.t * string = function
    f :: [] -> (s, f)
  | f :: t -> functions_and_file (StringSet.add f s) t
  | [] -> failwith("The list must have at least one element")

let () =
    Arg.parse [("--clang", Arg.Set_string clang_opts, "Pass option string to Clang")] (fun filename -> input_files := filename :: !input_files) usage_msg;;
    let idx = create_index ~exclude_declarations_from_pch:true ~display_diagnostics:true;;
    let (funs, file) = functions_and_file StringSet.empty !input_files in
    match Clang.Ast.parse_file ~index:idx ~command_line_args:(String.split_on_char ' ' !clang_opts) ~unsaved_files:[] ~options:Ast.Options.default file with
        { desc={ filename=f; items=i }; decoration=_ } -> print_endline f; List.iter (fun (fname, stmt) -> print_endline fname;  print_endline (match stmt with ConvSuccess s -> CFGKATExp.pprint s | ConvFailure e -> failwith e)) (List.filter_map convert_function (List.filter (decl_in_function_set funs) i))
