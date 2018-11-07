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
  "stateの各値を取得する" >::
    (fun _ ->
      assert_equal "q0" (Dfa.get_state_name st1);
      assert_equal false (Dfa.is_accepting st2);
      assert_equal ["q0"; "q1"] (Dfa.get_state_path_list st1)
    )
;;

let get_state_test =
  "stateの名前を探す。ない時はException" >::
    (fun _ ->
      assert_equal st1 (Dfa.get_state states "q0");
      assert_equal st2 (Dfa.get_state states "q4");
      assert_raises (Dfa.InvalidState "hoge") (fun _ -> Dfa.get_state states "hoge");
    )
;;

let transition_test =
  "statesの経路を辿った状態を返す" >::
    (fun _ ->
      assert_equal (Dfa.get_state states "q1") (Dfa.transition_state states (Dfa.get_state states "q0") [One]);
      assert_equal (Dfa.get_state states "q4") (Dfa.transition_state states (Dfa.get_state states "q0") [One; Zero; Zero; One]);
    )
;;

let accepting_language_test =
  "statesの経路を辿って受理されるか否か" >::
    (fun _ ->
      assert_equal true (Dfa.is_accepting_language states [ One; One; One; One]);
      assert_equal false (Dfa.is_accepting_language states [ One; One; One; One; One]);
    )
;;

let sort_legex_test =
  "legexのリストを統一された順番でソートする。意味が異なってはいけない" >::
    (fun _ ->
      assert_equal [Dfa.Empty; Union [Epsilon; Alpha Zero]; Concat [State "b"; State "a"]; Star (Union [State "a"; Alpha One; Concat [Empty]])] (Dfa.sort_legex_list [ Star(Union[Alpha One; State "a"; Concat [Empty]]); Concat [ State "b"; State "a" ]; Union [ Epsilon; Alpha Zero]; Empty]);
      assert_equal [Dfa.Concat [State "b"; State "c"; State "a"; Union [State "a"; State "b"; State "c"]]] (Dfa.sort_legex_list [Concat [State "b"; State "c"; State "a"; Union [State "b"; State "c"; State "a"]]]);
    )
;;

let concatinate_test =
  "legexをconcatinateするとき、意味を変えずに冗長なかっこが増えないようにする" >::
    (fun _ ->
      assert_equal (Dfa.Concat [Dfa.Union [Alpha Zero; Alpha One]; State "a"]) (Dfa.concatinate_legex (Dfa.Union [Alpha Zero; Alpha One]) (State "a"));
      assert_equal (Dfa.Concat [Dfa.Alpha Zero; Dfa.Alpha One; Dfa.Alpha Zero]) (Dfa.concatinate_legex (Dfa.Alpha Zero) (Concat [Dfa.Alpha One; Dfa.Alpha Zero]));
      assert_equal (Dfa.Empty) (Dfa.concatinate_legex Dfa.Epsilon Dfa.Empty);
    )
;;

let normalize_legex_test =
  "冗長な包括をなくす。また、Emptyの処理をうまくする" >::
    (fun _ ->
      assert_equal (Dfa.Alpha Zero) (Dfa.normalize_legex (Dfa.Union [Alpha Zero]));
      assert_equal (Dfa.Union [Alpha Zero; Alpha One]) (Dfa.normalize_legex (Dfa.Union [Dfa.Union[Dfa.Alpha Zero]; Dfa.Concat[Dfa.Alpha One]]));
      assert_equal (Dfa.Empty) (Dfa.normalize_legex (Dfa.Concat [Dfa.Union [Alpha One; Alpha Zero]; Dfa. Empty]))
    )

let tests =
  "all_tests" >::: [ 
    alpha_num_test;
    state_test;
    get_state_test;
    accepting_language_test;
    sort_legex_test;
    concatinate_test;
    normalize_legex_test;
  ];;
