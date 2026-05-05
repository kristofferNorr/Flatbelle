(*  Title:      
    Author:     Kristoffer Norrman

Flatbelle tools for Isar proof reconstruction.
*)

fun print_goal ctxt =
  let
    val st = Proof.goal_state ctxt;
    val goal = Thm.term_of (Thm.cprem_of st 1);
    val _ = tracing (Syntax.string_of_term ctxt goal);
  in
    all_tac (* Do nothing, just print the goal *)
  end;
