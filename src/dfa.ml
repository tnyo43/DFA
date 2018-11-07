
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
            else res
    in
    match lgx1, lgx2 with
    | State x1, State x2 -> if x1 < x2 then (-1) else if x1 = x2 then 0 else 1
    | Alpha x1, Alpha x2 -> 
        let a1 = alpha_to_string x1 in
        let a2 = alpha_to_string x2 in
        if a1 < a2 then (-1) else if a1 = a2 then 0 else 1
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
  let rec normalize_legex lgx: legex =
    match lgx with
    | Union [l] -> normalize_legex l
    | Union lst -> sort_if_lgx_list @@ List.fold_right (fun x -> (fun res -> (unite_legex (normalize_legex x) res))) lst Empty
    | Concat [l] -> normalize_legex l
    | Concat (Union lst :: t) -> 
        begin
          match t with
          | [Empty] -> Empty
          | _ -> sort_if_lgx_list @@ unite_legex_list @@ List.map (fun x -> concatinate_legex x (Concat t)) lst
        end
    | Concat lst -> sort_if_lgx_list @@ List.fold_right (fun x -> (fun res -> (concatinate_legex (normalize_legex x) res))) lst Epsilon
    | x -> x
  in
  sort_if_lgx_list @@ normalize_legex lgx
;;

let remove_state_legex (st: string) (lgx:legex) : legex =
  let rec classify lst left right=
    match lst with
    | [] -> (left, right)
    | h::t ->
        match h with
        | Concat clst ->
            if List.length clst > 0 && List.hd clst = State st then classify t (normalize_legex (Concat (List.tl clst)) :: left) right
            else classify t left (h :: right)
        | _ -> classify t left (h :: right)
  in
  match lgx with
  | Union ulst ->
      begin
        let (s, o) = classify ulst [] [] in
        let star = List.rev s in
        let others = List.rev o in
        match star with
        | [] -> Union others
        | _ -> normalize_legex (Concat [normalize_legex (Union others); Star (normalize_legex (Union star))])
      end
  | _ -> lgx
;;

type state' = S' of string * bool * string list * legex;;

let get_legex (s: string) (states: state list): legex = 
  let get_alphabet lst =
    if List.length lst = 1 then Zero
    else One
  in
  (* nameというstateのpathの中にsが含まれていれば追加 *)
  let rec init_legex (name:string) (path:string list) k : legex =
    match path with
    | [] -> k Empty
    | h::t ->
        if h = s then 
          begin
            if name="s" then init_legex name t (fun x -> k (unite_legex (Alpha (get_alphabet t)) x))
            else init_legex name t (fun x -> k (unite_legex (concatinate_legex (State name) (Alpha (get_alphabet t))) x))
          end
        else init_legex name t k
  in
  let rec get_legex (states: state list): legex = 
    match states with
    | [] -> Empty
    | h::t ->
        match h with
        | S (s, _, path) -> unite_legex (init_legex s path (fun x -> x)) (get_legex t)
  in get_legex states;;
;;

let states_to_states' states =
  let state_to_state' states state =
    match state with
    | S (sname, acc, path) ->
        if sname="s" then S' (sname, acc, path, Epsilon)
        else S' (sname, acc, path, normalize_legex @@ get_legex sname states)
  in
  List.map (state_to_state' states) states
;;

let state_replace_itself st =
  match st with
  | S' (sname, acc, path, lgx) -> S' (sname, acc, path, remove_state_legex sname lgx)
;;

let substitute_legex base var value: legex =
  let rec substitute_legex_union ulst =
    match ulst with
    | [] -> Union []
    | h::t -> unite_legex (substitute_legex h) @@ substitute_legex_union t
  and substitute_legex_concat clst =
    match clst with
    | [] -> Concat []
    | h::t -> concatinate_legex (substitute_legex h) @@ substitute_legex_concat t
  and substitute_legex lgx =
    match lgx with
    | Union lst -> substitute_legex_union lst
    | Concat lst -> substitute_legex_concat lst
    | State s ->
        if lgx = var then value else lgx
    | Star l -> Star (substitute_legex l)
    | x -> x
  in
  normalize_legex @@ substitute_legex base
;;


let states : state list =
  [
    S ("s", false, ["q0"; "q1"]); (* 初期状態 *)
    S ("q0", true, ["q0"; "q1"]); (* 受理状態 *)
    S ("q1", false, ["q2"; "q3"]);
    S ("q2", false, ["q4"; "q0"]);
    S ("q3", false, ["q1"; "q2"]);
    S ("q4", false, ["q3"; "q4"]);
  ]
;;

let states' = states_to_states' states;;

let base = Union [Concat [State "q4"; Alpha Zero]; Concat [State "q3"; Alpha One]];;
let var = State "q4";;
let value = Union [Concat [State "q1"; Alpha Zero]; Concat [State "q2"; Alpha One]];;
