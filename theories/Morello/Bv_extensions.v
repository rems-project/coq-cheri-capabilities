From stdpp.unstable Require Import bitvector bitvector_tactics.


Lemma bv_wrap_of_smaller_wrap n m b:
  (m <= n)%N ->
  bv_wrap n (bv_wrap m b) = bv_wrap m b.
Proof.
  intros ?. rewrite bv_wrap_small; [ reflexivity |].
  assert (0 ≤ bv_wrap m b < bv_modulus m)%Z by apply bv_wrap_in_range.
  assert (P: (m <= n)%N) by lia. 
  apply bv_modulus_le_mono in P. 
  lia.   
  Qed.
  
Lemma bv_wrap_of_larger_wrap_sum n m (b : bv 129) :
  (m < n)%N ->  
  bv_wrap m (bv_wrap n (bv_unsigned b) + 16) = bv_wrap m (bv_unsigned b + 16).
Proof.
  intros ?.
  replace (bv_wrap m (bv_wrap n (bv_unsigned b) + 16)) with (bv_wrap m (bv_wrap n ((bv_wrap n (bv_unsigned b) + 16))));
  [ rewrite bv_wrap_add_idemp_l; rewrite bv_wrap_bv_wrap; [ reflexivity | lia ] 
  | rewrite bv_wrap_bv_wrap; [ reflexivity | lia ]; reflexivity ].
  Qed.

Lemma bv_extract_idemp n m (b : bv n) : 
  bv_extract 0 m (bv_extract 0 m b) = bv_extract 0 m b.
Proof. 
  apply bv_eq_wrap. rewrite bv_extract_0_unsigned. 
  apply bv_wrap_bv_wrap. lia.
  Qed.

Lemma bv_extract_full n (b : bv n) :
  bv_extract 0 n b = b.
Proof. 
  apply bv_eq_wrap. rewrite bv_extract_0_unsigned. 
  apply bv_wrap_bv_wrap. lia.
  Qed.

Global Hint Rewrite bv_wrap_of_smaller_wrap using lia : bv_simplify.
Global Hint Rewrite bv_wrap_of_larger_wrap_sum using lia : bv_simplify.
Global Hint Rewrite bv_extract_idemp : bv_simplify.
Global Hint Rewrite bv_extract_full : bv_simplify.
Global Hint Rewrite @bv_extract_0_unsigned : bv_simplify.
Global Hint Rewrite @bv_and_unsigned : bv_simplify.


(** * Light versions of the [bv_simplify], [bv_simplify_arith] and [bv_solve] tactics from stdpp's bitvector *)

Tactic Notation "bv_simplify_light" :=
  autorewrite with bv_simplify;
  lazymatch goal with
  | |- _ =@{bv _} _ => apply bv_eq_wrap
  | |- not (_ =@{bv _} _) => apply bv_neq_wrap
  | _ => idtac
  end;
  bv_unfold;
  autorewrite with bv_unfolded_simplify.

Tactic Notation "bv_simplify_arith_light" :=
  bv_simplify_light;
  autorewrite with bv_unfolded_to_arith.

Ltac bv_solve_light :=
  bv_simplify_arith_light;
  unfold bv_signed, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus, bv_unsigned;
  simpl;
  lia.

Ltac bv_simp_r := repeat bv_simplify.
Tactic Notation "bv_simp_r" := bv_simp_r.
Tactic Notation "bv_simp_r" ident(H) :=
  repeat (bv_simplify H).
  
