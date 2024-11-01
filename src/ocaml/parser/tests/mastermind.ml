type config = {
  num_pegs : int;
  max_color : int;
  max_turns : int;
}

type state_label =
  | Player1ToProvideCode
  | Player2ToProvideCode
  | Player1ToGuess
  | Player2ToGuess
  | Player1Wins
  | Player2Wins
  | Draw
  | DrawByMaxTurns

type state = {
  label : state_label;
  player1_code : int list; (* should be a cryptographic hash *)
  player2_code : int list; (* should be a cryptographic hash *)
  player1_guess : int list option;
  player2_guess : int list option;
  player1_score : (int * int) option;
  player2_score : (int * int) option;
  turn : int;
}

let valid_input code num_pegs max_color =
  if List.length code <> num_pegs then false
  else List.for_all (fun peg_color -> peg_color <= max_color) code

let score guess code =
  let exact_matches, filtered_guess, filtered_code =
    List.fold_left2
      (fun (acc_exact_matches, acc_filtered_guess, acc_filtered_code) g c ->
        if g = c then
          (acc_exact_matches + 1, acc_filtered_guess, acc_filtered_code)
        else (acc_exact_matches, g :: acc_filtered_guess, c :: acc_filtered_code))
      (0, [], []) guess code
  in

  let rec count_color_only g c acc =
    match g with
    | [] -> acc
    | g_hd :: g_tl ->
      if List.mem g_hd c then
        let c_removed = List.filter (fun x -> x <> g_hd) c in
        count_color_only g_tl c_removed (acc + 1)
      else count_color_only g_tl c acc
  in

  let color_only_matches = count_color_only filtered_guess filtered_code 0 in

  (exact_matches, color_only_matches)

let transition config state input =
  match state.label with
  | Player1Wins | Player2Wins | Draw | DrawByMaxTurns -> state
  | Player1ToProvideCode ->
    assert (valid_input input config.num_pegs config.max_color) ;
    { state with label = Player2ToProvideCode; player1_code = input }
  | Player2ToProvideCode ->
    assert (valid_input input config.num_pegs config.max_color) ;
    { state with label = Player1ToGuess; player2_code = input }
  | Player1ToGuess -> (
    assert (valid_input input config.num_pegs config.max_color) ;
    let state =
      { state with label = Player2ToGuess; player1_guess = Some input }
    in
    match state.player2_guess with
    | None -> state
    | Some player2_guess ->
      {
        state with
        player2_score = Some (score player2_guess state.player1_code);
      })
  | Player2ToGuess -> (
    assert (valid_input input config.num_pegs config.max_color) ;
    let state = { state with player2_guess = Some input } in
    let state =
      match state.player1_guess with
      | None -> state
      | Some player1_guess ->
        {
          state with
          player1_score = Some (score player1_guess state.player2_code);
        }
    in
    let player1_finished = state.player1_score = Some (config.num_pegs, 0) in
    let player2_finished = state.player2_score = Some (config.num_pegs, 0) in
    match (player1_finished, player2_finished) with
    | false, false ->
      if state.turn = config.max_turns then
        { state with label = DrawByMaxTurns }
      else { state with label = Player1ToGuess; turn = state.turn + 1 }
    | true, false -> { state with label = Player1Wins }
    | false, true -> { state with label = Player2Wins }
    | true, true -> { state with label = Draw })

let run_game config state inputs =
  List.fold_left
    (fun acc_state guess -> transition config acc_state guess)
    state inputs

let init_state =
  {
    label = Player1ToProvideCode;
    player1_code = [];
    player2_code = [];
    player1_guess = None;
    player2_guess = None;
    player1_score = None;
    player2_score = None;
    turn = 0;
  }

let () =
  let config = { num_pegs = 4; max_color = 5; max_turns = 10 } in
  let inputs =
    [ [ 0; 1; 2; 3 ]; (* player1 code *) [ 2; 3; 4; 5 ] (* player2 code *) ]
  in
  let state = run_game config init_state inputs in
  assert (state.player1_guess = None) ;
  assert (state.player2_guess = None) ;
  assert (state.label = Player1ToGuess) ;
  let inputs =
    [
      (* player1 guesses but can't score player2 yet *)
      [ 5; 3; 4; 5 ];
      (* player2 guesses and scores player1 *)
      [ 4; 4; 4; 3 ];
    ]
  in
  let state = run_game config state inputs in
  assert (state.player1_score = Some (3, 0)) ;
  assert (state.player2_score = None) ;
  assert (state.label = Player1ToGuess) ;
  (* player1 guesses and scores player2*)
  let state = transition config state [ 2; 3; 4; 5 ] in
  assert (state.player2_score = Some (1, 0)) ;
  (* player2 guesses and scores player1*)
  let state = transition config state [ 4; 1; 4; 3 ] in
  assert (state.player1_score = Some (4, 0)) ;
  assert (state.player2_score = Some (1, 0)) ;
  assert (state.label = Player1Wins)
