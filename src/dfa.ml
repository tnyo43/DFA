
type alphabet = | Zero | One;;
let alphabet_num = 2;;

let alpha_to_num a =
  match a with
  | Zero -> 0
  | One -> 1
;;

let alpha_to_string a = string_of_int @@ alpha_to_num a;;

type state = S of string * bool * string list;;
exception InvalidState of string;;

let make_state sname acc path = S (sname, acc, path);;

let get_state_name s =
  match s with
  | S (sname, _, _) -> sname
;;

let is_accepting s =
  match s with
  | S (_, acc, _) -> acc
;;

let get_state_path_list s =
  match s with
  | S (_, _, path) -> path
;;

(* stsの中からsnameという名前のstateを返す *)
let get_state (sts: state list) (sname:string): state =
  let rec get_state idx =
    let s = List.nth sts idx in
    match s with S(sname', _, _) ->
      if sname = sname' then s
      else if idx+1 >= List.length sts then raise (InvalidState sname)
      else get_state @@ idx+1
  in
  get_state 0
;;

let transition_state (sts: state list) (st: state) (lang: alphabet list): state =
  let rec transition lang (st: state) : state =
    match lang with
    | [] -> st
    | h::t ->
        begin
          match st with
          | S (_, _, path) -> transition t @@ get_state sts @@ List.nth path @@ alpha_to_num h
        end
  in
  transition lang st
;;

let is_accepting_language (sts: state list) (lang: alphabet list): bool = 
  let st = get_state sts "s" in
  is_accepting @@ transition_state sts st lang
;;

(* 正規表現のタイプ。省略形は"leg" *)
type legex =
  | State of string
  | Alpha of alphabet
  | Epsilon (* 長さ0の言語 *)
  | Empty (* 空集合 *)
  | Union of legex list (* 積 *)
  | Concat of legex list (* 接続 *)
  | Star of legex (* 0回以上の繰り返し *)
;;

let legex_type_to_num lgx =
  match lgx with
  | Empty -> (-1)
  | Epsilon -> 0
  | State _ -> 1
  | Alpha _ -> 2
  | Union _ -> 3
  | Concat _ -> 4
  | Star _ -> 5
;;

let rec compare_legex lgx1 lgx2 =
  let n1 = legex_type_to_num lgx1 in
  let n2 = legex_type_to_num lgx2 in
  if n1 < n2 then (-1)
  else if n1 > n2 then 1
  else
    let rec compare_legex_list lst1 lst2 =
      match lst1 with
      | [] -> if lst2 = [] then 0 else 1
      | h::t ->
          if lst2 = [] then (-1)
          else 
            let res = compare_legex h @@ List.hd lst2 in
            if res = 0 then compare_legex_list t @@ List.tl lst2
            else 0
    in
    match lgx1, lgx2 with
    | State x1, State x2 -> if x1 < x2 then (-1) else 1
    | Alpha x1, Alpha x2 -> if (alpha_to_string x1) < (alpha_to_string x2) then (-1) else 1
    | Union lst1, Union lst2 -> compare_legex_list lst1 lst2
    | Concat lst1, Concat lst2 -> compare_legex_list lst1 lst2
    | _ -> failwith "something wrong"
;;

let rec sort_legex_list (lst: legex list): legex list = 
  List.sort compare_legex @@ List.map sort_if_lgx_list lst
and  sort_if_lgx_list lgx =
  match lgx with
  | Union lst -> Union (sort_legex_list lst)
  | Concat lst -> Concat (List.map sort_if_lgx_list lst)
  | Star x -> Star (sort_if_lgx_list x)
  | x -> x
;;

let unite_legex_list lst =
  match lst with
  | [] -> Empty
  | h::[] -> h
  | h::t -> Union lst
;;

let unite_legex l1 l2 =
  match l1 with
  | Empty -> l2
  | Union lst1 ->
      begin
        match l2 with
        | Empty -> l1
        | Union lst2 -> Union (lst1 @ lst2)
        | x -> unite_legex_list (x::lst1)
      end
  | x -> 
    begin
        match l2 with
        | Empty -> l1
        | Union lst2 -> unite_legex_list (x::lst2)
        | m -> Union [l1; l2]
    end
;;

let concatinate_legex l1 l2 =
  match l1 with
  | Epsilon -> l2
  | Empty -> Empty
  | Concat x -> 
      begin
        match l2 with
        | Epsilon -> l1
        | Empty -> Empty
        | Concat y -> Concat (x@y)
        | y -> Concat (x@[y])
      end
  | x ->
      begin 
        match l2 with
        | Epsilon -> l1
        | Empty -> Empty
        | Concat y -> Concat (x::y)
        | y -> Concat ([x;y])
      end
;;

let normalize_legex lgx =
  let rec normalize_legex lgx =
    match lgx with
    | Union [l] -> normalize_legex l
    | Union lst -> sort_if_lgx_list @@ List.fold_right (fun x -> (fun res -> (unite_legex (normalize_legex x) res))) lst Empty
    | Concat [l] -> normalize_legex l
    | Concat lst -> sort_if_lgx_list @@ List.fold_right (fun x -> (fun res -> (concatinate_legex (normalize_legex x) res))) lst Epsilon
    | x -> x
  in
  sort_if_lgx_list @@ normalize_legex lgx
;;




