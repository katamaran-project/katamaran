
    (* #[export] Instance purespecm : CPureSpecM CPureSpec := *)
    (*   {| CPureSpecM.pure                  := @pure; *)
    (*      CPureSpecM.bind                  := @bind; *)
    (*      CPureSpecM.error                 := @error; *)
    (*      CPureSpecM.block                 := @block; *)
    (*      CPureSpecM.angelic               := @angelic; *)
    (*      CPureSpecM.demonic               := @demonic; *)
    (*      CPureSpecM.angelic_ctx           := @angelic_ctx; *)
    (*      CPureSpecM.demonic_ctx           := @demonic_ctx; *)
    (*      CPureSpecM.assert_pathcondition  := @assert_pathcondition; *)
    (*      CPureSpecM.assert_formula        := @assert_formula; *)
    (*      CPureSpecM.assume_pathcondition  := @assume_pathcondition; *)
    (*      CPureSpecM.assume_formula        := @assume_formula; *)
    (*      CPureSpecM.angelic_binary        := @angelic_binary; *)
    (*      CPureSpecM.demonic_binary        := @demonic_binary; *)
    (*      CPureSpecM.angelic_pattern_match := @angelic_pattern_match; *)
    (*      CPureSpecM.demonic_pattern_match := @demonic_pattern_match; *)
    (*      CPureSpecM.new_pattern_match     := @new_pattern_match; *)
    (*      CPureSpecM.debug                 := fun _ m => m; *)
    (*   |}. *)

    (* #[global] Arguments CPureSpec.pure {_} _ /. *)
    (* #[global] Arguments CPureSpec.error {_} /. *)
    (* #[global] Arguments CPureSpec.bind {_ _} _ _ _ /. *)
    (* #[global] Arguments CPureSpec.assert_formula _ /. *)
    (* #[global] Arguments CPureSpec.assert_pathcondition _ /. *)
    (* #[global] Arguments CPureSpec.assume_formula _ /. *)
    (* #[global] Arguments CPureSpec.assume_pathcondition _ /. *)
    (* #[global] Arguments CPureSpec.angelic_binary {_} _ _ /. *)
    (* #[global] Arguments CPureSpec.demonic_binary {_} _ _ /. *)


    (* #[export] Instance mon_purespecm : MPureSpecM CPureSpec. *)
    (* Proof. constructor; try typeclasses eauto. Qed. *)
