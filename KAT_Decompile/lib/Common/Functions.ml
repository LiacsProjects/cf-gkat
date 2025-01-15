(** Generic Helper functions *)

(** Cartisian product of two lists*)
let list_prod (l : 'a list) (l' : 'b list) : ('a * 'b) list =
  List.concat (List.map (fun e -> List.map (fun e' -> (e, e')) l') l)

(** Like powerset but for list
    All the elements in the resulting sub lists maintains their original order.*)
let rec power_list (l : 'a list) : 'a list list =
  let ( let* ) l f = List.concat_map f l in
  match l with
  | [] -> [ [] ]
  | h :: tail ->
      let* sub_tail = power_list tail in
      [ h :: sub_tail; sub_tail ]

(** Monadic map on list with option monad.
  
the map will exit immediately when a None is encountered.
And element that results in Some None will be removed.
This uses difference list technique to keep the map function efficent
https://stackoverflow.com/questions/27386520/tail-recursive-list-map*)
let list_filter_map_m_opt (f : 'a -> 'b option option) (lst : 'a list) :
    'b list option =
  let rec map_aux (acc : 'b list -> 'b list option) : 'a list -> 'b list option
      = function
    | [] -> acc []
    | x :: xs ->
        Option.bind (f x) (fun y_opt ->
            map_aux
              (fun ys ->
                match y_opt with Some y -> acc (y :: ys) | None -> acc ys)
              xs)
  in
  map_aux Option.some lst

(** Given a "recursive function" that compute the one result,
    compute all of the result for each 'a, and arrange in a list,
    the result is in the order of `inp`.

    The first argument of `comp_one_rec` is itself for recursion,
    except the first argument can return None, indicating a finite recursion.
    This function will cache the result of each computation to speed up recursion*)
let compute_map_rec (comp_one_rec : ('a -> 'b option) -> 'a -> 'b)
    (inps : 'a list) : ('a * 'b) list =
  (* the value is marked None, when we are in the process of computing *)
  let memo_tbl : ('a, 'b option) Hashtbl.t =
    Hashtbl.create (List.length inps)
  in
  (* Compute the result of `inp`, return None when there is a infinte loop*)
  let rec comp_one_opt inp =
    match Hashtbl.find_opt memo_tbl inp with
    | Some res -> res
    | None -> Some (compute_one inp)
  (* Compute the result of `inp`, when the `inp` is not found in the hashtable
     the infinite loop is already handled by `comp_one_rec` *)
  and compute_one inp =
    Hashtbl.add memo_tbl inp None;
    let res = comp_one_rec comp_one_opt inp in
    Hashtbl.replace memo_tbl inp (Some res);
    res
  in
  List.map
    (fun inp ->
      ( inp,
        match Hashtbl.find_opt memo_tbl inp with
        | Some (Some res) -> res
        | None -> compute_one inp
        | Some None ->
            failwith
              "Memory table contains None between computing two elements, this \
               is a bug" ))
    inps

(** __IMPURE__, like all the queue functions
    Convert a list into a queue*)
let queue_push_list (queue : 'a Queue.t) (l : 'a list) : unit =
  List.iter (fun elem -> Queue.push elem queue) l

