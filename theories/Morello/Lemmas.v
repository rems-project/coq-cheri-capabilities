From SailStdpp Require Import Base Values Values_lemmas Operators_mwords MachineWord Operators_mwords MachineWordInterface.

From stdpp Require Import list_numbers bitvector bitvector_tactics bitblast.

From CheriCaps.Common Require Import Utils.
From CheriCaps.Morello Require Import CapFns Capabilities.

(** More automation for modular arithmetics. *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

Local Ltac reduce_closed_N_tac ::=
  repeat match goal with
  | |- context [bv ?n] => progress reduce_closed (bv n)
  | H : context [bv ?n] |- _ => progress reduce_closed (bv n)
  | |- context [MachineWord.MachineWord.word ?n] => progress reduce_closed (MachineWord.MachineWord.word n)
  | H : context [MachineWord.MachineWord.word ?n] |- _ => progress reduce_closed (MachineWord.MachineWord.word n)
  | |- context [N.of_nat ?n] => progress reduce_closed (N.of_nat n)
  | H : context [N.of_nat ?n] |- _ => progress reduce_closed (N.of_nat n)
  end.

Section mword_lemmas.
  Open Scope Z.

  Lemma mword_eq_vec_bv_unsigned n (x y : Values.mword n) :
    (Operators_mwords.eq_vec x y) = (bv_unsigned (Values.get_word x) =? bv_unsigned (Values.get_word y))%Z.
  Proof.
    unfold Operators_mwords.eq_vec, MachineWord.MachineWord.eqb, MachineWord.MachineWord.eq_dec.
    set (a := Values.get_word x). 
    set (b := Values.get_word y).
    destruct (base.decide (a = b)) as [e | e].
    { apply bv_eq in e. by rewrite <- Z.eqb_eq in e. }
    unfold not in e.
    symmetry. apply not_true_is_false.
    unfold not. intro H.   
    apply e.
    apply Z.eqb_eq in H. by apply bv_eq.
  Qed.

  Lemma mword_neq_vec_bv_unsigned n {x y : Values.mword n} :
    (Operators_mwords.neq_vec x y) = negb (bv_unsigned (Values.get_word x) =? bv_unsigned (Values.get_word y))%Z.
  Proof.
    unfold Operators_mwords.neq_vec.
    by rewrite mword_eq_vec_bv_unsigned.
  Qed.

  Lemma mwords_update_subrange_bv (c : (*Capability.t*) bv 129) hi lo (o : Values.mword (hi-(lo-1))) :
    hi < 129 ->
    hi >= lo ->
    lo >= 0 ->
    Operators_mwords.update_subrange_vec_dec (c : Values.mword 129) hi lo o
    = bv_concat 129 
        (bv_extract (Z.to_N (hi+1)) (129 - Z.to_N (hi+1)) c) 
        (@bv_concat (Z.to_N (hi+1)) _ _ (mword_to_bv o) (bv_extract 0 (Z.to_N lo) c)).
  Proof.
    intros H_hi_max H_hi_min H_lo.
    unfold Operators_mwords.update_subrange_vec_dec, MachineWord.MachineWord.update_slice, MachineWord.MachineWord.slice.
    replace (N.of_nat (Z.to_nat lo + Z.to_nat (hi - (lo - 1)))) with (Z.to_N (hi + 1)); [| lia]. 
    replace (N.of_nat (Z.to_nat 129 - Z.to_nat (hi - (lo - 1)) - Z.to_nat lo)) with (129 - Z.to_N (hi + 1))%N; [| lia].
    replace (N.of_nat (Z.to_nat lo)) with (Z.to_N lo); [| lia].
    reflexivity.
  Qed.

  Lemma mwords_objtype_update_subrange_bv (c : (*Capability.t*) bv 129) (o : bv 15) :
    Operators_mwords.update_subrange_vec_dec (c : Values.mword 129) CapFns.CAP_OTYPE_HI_BIT CapFns.CAP_OTYPE_LO_BIT o
    = bv_concat 129 (bv_extract 110 19 c) (bv_concat 110 o (bv_extract 0 95 c)).
  Proof.
    unfold CapFns.CAP_OTYPE_HI_BIT, CapFns.CAP_OTYPE_LO_BIT. rewrite mwords_update_subrange_bv; done.
  Qed.

  Lemma mwords_perms_update_subrange_bv (c : (*Capability.t*) bv 129) (p : bv 18) :
    Operators_mwords.update_subrange_vec_dec (c : Values.mword 129) CapFns.CAP_PERMS_HI_BIT CapFns.CAP_PERMS_LO_BIT p 
    = bv_concat 129 (bv_extract 128 1 c) (bv_concat 128 p (bv_extract 0 110 c)).
  Proof. 
    unfold CapFns.CAP_PERMS_HI_BIT, CapFns.CAP_PERMS_LO_BIT. rewrite mwords_update_subrange_bv; done.
  Qed.

  Lemma mwords_perms_subrange_bv (c : bv 18) : 
    Operators_mwords.subrange_vec_dec (c : Values.mword 18) (CapFns.CAP_PERMS_NUM_BITS-1) 0 
    = bv_extract 0 18 c.
  Proof.  
    unfold CapFns.CAP_PERMS_NUM_BITS, CapFns.CAP_PERMS_HI_BIT, CapFns.CAP_PERMS_LO_BIT. 
    unfold Operators_mwords.subrange_vec_dec, MachineWord.MachineWord.slice. reflexivity.
  Qed.

  Lemma mwords_permsext_subrange_bv (c : bv 64) : 
    Operators_mwords.subrange_vec_dec (c : Values.mword 64) (CapFns.CAP_PERMS_NUM_BITS-1) 0 
    = bv_extract 0 18 c.
  Proof.  
    unfold CapFns.CAP_PERMS_NUM_BITS, CapFns.CAP_PERMS_HI_BIT, CapFns.CAP_PERMS_LO_BIT. 
    unfold Operators_mwords.subrange_vec_dec, MachineWord.MachineWord.slice. reflexivity.
  Qed.
  
End mword_lemmas.

Section Cap_translation_lemmas.

  Lemma cap_permits_store_bv_and (c:Capability.t) : 
    Capability.cap_permits_store c →  
    bv_and c (BV 129 (2^126)) = BV 129 (2^126).
  Proof. 
    Capability.unfold_cap. unfold Capability.t, Capability.len in *.
    intro H. case_decide as H0; [| done ]. bv_simplify.    
    bv_simplify H0. 
    bitblast as n.
    by bitblast H0 with (n - 110).
  Qed.

  Lemma cap_permits_load_bv_and (c:Capability.t) : 
    Capability.cap_permits_load c -> 
    bv_and c (BV 129 (2^127)) = BV 129 (2^127).
  Proof. 
    Capability.unfold_cap. unfold Capability.t, Capability.len in c.
    intro H. case_decide as H0; [| done ]. bv_simplify.   
    bv_simplify H0.
    bitblast as n.
    by bitblast H0 with (n - 110).
  Qed.

  Lemma cap_is_unsealed_eq_vec (c : Capability.t ): 
    Capability.cap_is_unsealed c <-> Operators_mwords.eq_vec (CapFns.CapGetObjectType c) (MachineWord.MachineWord.zeros (Pos.to_nat (63 + 1))) = true.
  Proof. 
    split.
    - intro H. unfold Capability.cap_is_unsealed, Capability.cap_is_sealed, CapFns.CapIsSealed, CapFns.Zeros, Operators_mwords.neq_vec, CapFns.CAP_VALUE_NUM_BITS, CapFns.CAP_VALUE_HI_BIT, CapFns.CAP_VALUE_LO_BIT in H. apply Is_true_true_1. simpl in H. 
    rewrite negb_involutive in H. done. 
    - intro H. unfold Capability.cap_is_unsealed, Capability.cap_is_sealed, CapFns.CapIsSealed, CapFns.Zeros, Operators_mwords.neq_vec. simpl. rewrite H. done.
  Qed.

End Cap_translation_lemmas.

Section Cap_properties.

  Lemma perm_leq_executable c c':
    Capability.leq_perms c c' ->
    Capability.cap_permits_execute c ->
    Capability.cap_permits_execute c'.
  Proof.
    intros Hleq Hc.
    unfold Capability.leq_perms in Hleq.
    destruct (Capability.cap_permits_execute c), (Capability.cap_permits_execute c'); [ done | | done | done].
    + simpl in Hleq. by rewrite !Tauto.if_same in Hleq.
  Qed.

  Lemma perm_leq_unseal c c':
    Capability.leq_perms c c' ->
    Capability.cap_permits_unseal c ->
    Capability.cap_permits_unseal c'.
  Proof.
    intros Hleq Hc.
    unfold Capability.leq_perms in Hleq.
    destruct (Capability.cap_permits_unseal c), (Capability.cap_permits_unseal c'); [ done | | done | done].
    + simpl in Hleq. by rewrite !Tauto.if_same in Hleq.
  Qed.

  Lemma perm_leq_read c c':
    Capability.leq_perms c c' ->
    Capability.cap_permits_load c ->
    Capability.cap_permits_load c'.
  Proof.
    intros Hleq Hc.
    unfold Capability.leq_perms in Hleq.
    destruct (Capability.cap_permits_load c), (Capability.cap_permits_load c'); [ done | | done | done].
    + simpl in Hleq. by rewrite !Tauto.if_same in Hleq.
  Qed.

  Lemma perm_leq_write c c':
    Capability.leq_perms c c' ->
    Capability.cap_permits_store c ->
    Capability.cap_permits_store c'.
  Proof.
    intros Hleq Hc.
    unfold Capability.leq_perms in Hleq.
    destruct (Capability.cap_permits_store c), (Capability.cap_permits_store c'); [ done | | done | done].
    + simpl in Hleq. by rewrite !Tauto.if_same in Hleq.
  Qed.

  Lemma leq_bounds_spec {c c' b1 b2 b3 b4} :
    Capability.leq_bounds c' c ->
    Capability.cap_get_bounds c = (b1, b2) ->
    Capability.cap_get_bounds c' = (b3, b4) ->
    (bv_unsigned b1 ≤ bv_unsigned b3)%Z ∧
    (bv_unsigned b4 ≤ bv_unsigned b2)%Z.
  Proof.
    intros Hbounds Hc Hc'.
    unfold Capability.leq_bounds in Hbounds.
    rewrite Hc, Hc' in Hbounds.
    destruct (orb_prop_elim _ _ Hbounds) as [Hbounds' | Hbounds'].
    + destruct (andb_prop_elim _ _ Hbounds') as [Heq Heq'].
      rewrite !Z_eqb_is_eq in Heq, Heq'.
      lia.
    + destruct (andb_prop_elim _ _ Hbounds') as [Heq _].
      unfold Capability.bounds_contained, Capabilities.Bounds.contained in Heq.
      rewrite Hc, Hc' in Heq.
      destruct (andb_prop_elim _ _ Heq) as [Heq' Heq''].
      unfold geb, gtb, leb, ltb in Heq', Heq''.
      split.
      - apply orb_prop_elim in Heq'. destruct Heq' as [Heq' | Heq'].
        { apply Is_true_true_1, Z.ltb_lt in Heq'. lia. }
        apply Is_true_eq_true in Heq'.
        apply bv_eqb_eq in Heq'. apply bv_eq in Heq'. 
        lia.
      - apply orb_prop_elim in Heq''. destruct Heq'' as [Heq'' | Heq'']; apply Is_true_eq_true in Heq''.
        { rewrite Z.ltb_lt in Heq''. lia. }
        rewrite bv_eqb_eq in Heq''. apply bv_eq in Heq''. lia.
  Qed.

  Lemma leq_bounds_to_cap_aligned_addresses_subset c c' a:
    Capability.leq_bounds c' c ->
    a ∈ Capability.cap_aligned_addresses c' ->
    a ∈ Capability.cap_aligned_addresses c.
  Proof.
    intros Hbounds Hc'.
    unfold Capability.cap_aligned_addresses, Capability.cap_all_addresses in *.
    destruct (Capability.cap_get_bounds c) as [b1 b2] eqn:H1, (Capability.cap_get_bounds c') as [b3 b4] eqn:H2.
    destruct (leq_bounds_spec Hbounds H1 H2) as [Hb1 Hb2].
    rewrite !elem_of_list_filter in Hc'. rewrite !elem_of_list_filter.
    destruct Hc' as [? Hc'].
    split; [assumption| ].
    rewrite !elem_of_seqZ in *.
    assert (Capability.cap_align (bv_unsigned b1) ≤ Capability.cap_align (bv_unsigned b3))%Z as Halign.
    { unfold Capability.cap_align. lia. }
    lia.
  Qed.

  Lemma leq_bounds_to_cap_addresses_subset c c' a:
    Capability.leq_bounds c' c ->
    a ∈ Capability.cap_addresses c' ->
    a ∈ Capability.cap_addresses c.
  Proof.  
    intros Hbounds Hc'.
    unfold Capability.cap_addresses in *.
    destruct (Capability.cap_get_bounds c) as [b1 b2] eqn:H1, (Capability.cap_get_bounds c') as [b3 b4] eqn:H2.
    destruct (leq_bounds_spec Hbounds H1 H2) as [Hb1 Hb2].
    rewrite !elem_of_seqZ in *.
    assert (Capability.cap_align (bv_unsigned b1) ≤ Capability.cap_align (bv_unsigned b3))%Z as Halign.
    { unfold Capability.cap_align. lia. }
    lia.
  Qed.

  Lemma equal_bounds_to_equal_cap_aligned_addresses c c':
    Capability.cap_get_bounds c = Capability.cap_get_bounds c' ->
    Capability.cap_aligned_addresses c = Capability.cap_aligned_addresses c'.
  Proof.
    intros Hbounds.
    unfold Capability.cap_aligned_addresses, Capability.cap_all_addresses.
    by rewrite Hbounds.
  Qed.

End Cap_properties.
