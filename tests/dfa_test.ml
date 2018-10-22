open OUnit2

let alpha_num_test =
  "alpha to num" >:: 
    (fun _ ->
      assert_equal 0 (Dfa.alpha_to_num Zero);
      assert_equal 1 (Dfa.alpha_to_num One)
    )
;;

let st1 = Dfa.make_state "q0"  true ["q0"; "q1"];;
let st2 = Dfa.make_state "q4" false ["q3"; "q4"];;

let states = [
    Dfa.make_state  "s" false ["q0"; "q1"]; (* 初期状態 *)
    Dfa.make_state "q0"  true ["q0"; "q1"]; (* 受理状態 *)
    Dfa.make_state "q1" false ["q2"; "q3"];
    Dfa.make_state "q2" false ["q4"; "q0"];
    Dfa.make_state "q3" false ["q1"; "q2"];
    Dfa.make_state "q4" false ["q3"; "q4"];
];;

let state_test =
  "state name, accepting and path" >::
    (fun _ ->
      assert_equal "q0" (Dfa.get_state_name st1);
      assert_equal false (Dfa.is_accepting st2);
      assert_equal ["q0"; "q1"] (Dfa.get_state_path_list st1)
    )
;;

let get_state_test =
  "get state from states" >::
    (fun _ ->
      assert_equal (List.nth states 1) st1;
      assert_equal (List.nth states 5) st2;
      assert_raises (Dfa.InvalidState "hoge") (fun _ -> Dfa.get_state states "hoge");
    )
;;

let transition_test =
  "transition to other state" >::
    (fun _ ->
      assert_equal (Dfa.get_state states "q1") (Dfa.transition_state states (Dfa.get_state states "q0") [One]);
      assert_equal (Dfa.get_state states "q4") (Dfa.transition_state states (Dfa.get_state states "q0") [One; Zero; Zero; One]);
    )
;;

let accepting_language_test =
  "accept language" >::
    (fun _ ->
      assert_equal true (Dfa.is_accepting_language states [ One; One; One; One]);
      assert_equal false (Dfa.is_accepting_language states [ One; One; One; One; One]);
    )
;;

let tests =
  "all_tests" >::: [ 
    alpha_num_test;
    state_test;
    get_state_test;
    accepting_language_test;
  ];;
