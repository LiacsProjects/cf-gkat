open Clang2CFGKAT
open Clang
open Clang.Ast

let usage_msg = "comparecfgkat <file> <file> [<file> ...]"

let clang_opts = ref ""

let input_files = ref []

let is_local f : decl_desc node -> bool = function
    { desc=_; decoration=d } -> let l = location_of_decoration d in match l with Concrete { filename=g; _ } -> f = g | Clang cxl -> (match get_presumed_location cxl with (g, _, _) -> f = g)

let () =
    Arg.parse [("--clang", Arg.Set_string clang_opts, "Pass option string to Clang")] (fun filename -> input_files := filename :: !input_files) usage_msg;;
    let idx = create_index ~exclude_declarations_from_pch:true ~display_diagnostics:true;;
    let exps = List.map (fun f -> match Clang.Ast.parse_file ~index:idx ~command_line_args:(String.split_on_char ' ' !clang_opts) ~unsaved_files:[] ~options:Ast.Options.default f with { desc={ filename=k; items=i }; decoration=_ } -> (List.filter_map convert_function (List.filter (is_local k) i))) !input_files;;
    match exps with
        file1 :: file2 :: _ ->
            let keys = List.map fst file1 in
            print_endline ((string_of_int (List.length keys)) ^ " functions"); List.iter (fun k -> match (List.assoc k file1, List.assoc k file2) with
                (ConvSuccess f, ConvSuccess g) -> print_endline ("Function " ^ k ^ " " ^ (string_of_bool (CFGKATExp.Eq.equiv f g)))
              | (ConvFailure _, ConvSuccess _) -> print_endline ("Function " ^ k ^ " missing in file 1")
              | (ConvSuccess _, ConvFailure _) -> print_endline ("Function " ^ k ^ " missing in file 2")
              | (ConvFailure _, ConvFailure _) -> print_endline ("Function " ^ k ^ " missing in both files")
            ) keys
      | _ -> failwith ("At least two input files are required")
