
type alphabet = | Zero | One;;
let alphabet_num = 2;;

let alpha_to_num a =
  match a with
  | Zero -> 0
  | One -> 1
;;

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

