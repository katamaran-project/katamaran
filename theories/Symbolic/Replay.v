(******************************************************************************)
(* Copyright (c) 2020 Dominique Devriese, Georgy Lukyanov,                    *)
(*   Sander Huyghebaert, Steven Keuchel                                       *)
(* All rights reserved.                                                       *)
(*                                                                            *)
(* Redistribution and use in source and binary forms, with or without         *)
(* modification, are permitted provided that the following conditions are     *)
(* met:                                                                       *)
(*                                                                            *)
(* 1. Redistributions of source code must retain the above copyright notice,  *)
(*    this list of conditions and the following disclaimer.                   *)
(*                                                                            *)
(* 2. Redistributions in binary form must reproduce the above copyright       *)
(*    notice, this list of conditions and the following disclaimer in the     *)
(*    documentation and/or other materials provided with the distribution.    *)
(*                                                                            *)
(* THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS        *)
(* "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED  *)
(* TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR *)
(* PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR          *)
(* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,      *)
(* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,        *)
(* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR         *)
(* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF     *)
(* LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING       *)
(* NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS         *)
(* SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.               *)
(******************************************************************************)

From Katamaran Require Import
  Prelude
  Base
  Signature.

Import ctx.notations env.notations.

#[local] Set Implicit Arguments.

Module Type SymbolicReplayOn
  (Import B : Base)
  (Import SIG : Signature B).

  Import ModalNotations SPureSpecM SPureSpecM.notations.

  Definition reuseMsg :
    ⊢ AMessage -> □(SHeap -> AMessage) :=
    fun w msg w1 θ1 _h => persist msg θ1.

  Definition sreplay `{pureM : SPureSpecM M} :
    forall {Σ} (s : 𝕊 Σ), ⊢ Sub Σ -> M Unit :=
    fix replay {Σ} s {w0} δ {struct s} :=
      match s with
      | SymProp.angelic_binary o1 o2 =>
          SPureSpecM.angelic_binary (replay o1 δ) (replay o2 δ)
      | SymProp.demonic_binary o1 o2 =>
          SPureSpecM.demonic_binary (replay o1 δ) (replay o2 δ)
      | SymProp.block => block
      | SymProp.error msg =>
          error (reuseMsg (subst msg δ))
      | SymProp.assertk fml msg k =>
          ⟨ θ ⟩ _ <- assert_formula
                       (reuseMsg (subst msg δ))
                       (subst fml δ) ;;
          replay k (persist δ θ)
      | SymProp.assumek fml k =>
          ⟨ θ ⟩ _ <- assume_formula (subst fml δ) ;;
          replay k (persist δ θ)
      | SymProp.angelicv b k =>
          ⟨ θ ⟩ t <- angelic (Some (name b)) (type b) ;;
          replay k (env.snoc (persist δ θ) b t)
      | SymProp.demonicv b k =>
          ⟨ θ ⟩ t <- demonic (Some (name b)) (type b) ;;
          replay k (env.snoc (persist δ θ) b t)
      | SymProp.assert_vareq x t msg k =>
          let ζ    := sub_shift (b:=x∷_) _ in
          let msg  := subst msg ζ in
          let fml  := formula_relop bop.eq
                        (subst t ζ)
                        (term_var x) in
          ⟨ θ ⟩ _            <- assert_formula
                                  (reuseMsg (subst msg δ))
                                  (subst fml δ) ;;
          replay k (env.remove (x∷_) δ⟨θ⟩ _)
      | SymProp.assume_vareq x t k =>
          let ζ    := sub_shift (b:=x∷_) _ in
          let fml  := formula_relop bop.eq
                        (subst t ζ)
                        (term_var x) in
          ⟨ θ ⟩ _            <- assume_formula
                                  (subst fml δ) ;;
          replay k (env.remove (x∷_) δ⟨θ⟩ _)
      | SymProp.pattern_match s pat rhs =>
          error (fun _ _ _ => amsg.mk tt)
          (* FIXME *)
          (* ⟨ θ ⟩ '(existT pc δpc) <- new_pattern_match id pat (subst s δ) ;; *)
          (* replay (rhs pc) (persist δ θ ►► δpc) *)
      | SymProp.pattern_match_var x pat rhs =>
          error (fun _ _ _ => amsg.mk tt)
          (* FIXME *)
          (* ⟨ θ ⟩ '(existT pc δpc) <- new_pattern_match id pat (subst (term_var x) δ) ;; *)
          (* replay (rhs pc) (env.remove _ (δ⟨θ⟩ ►► δpc) _) *)
      | SymProp.debug msg k =>
          debug (reuseMsg (subst msg δ)) (replay k δ)
      end.

End SymbolicReplayOn.
