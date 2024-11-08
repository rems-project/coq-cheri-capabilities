Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Floats.PrimFloat.
Require Import Coq.Numbers.BinNums.
Require Import Coq.Vectors.Vector.
Require Import Coq.Strings.Ascii.
From Coq Require Import ssreflect Utf8.

From stdpp Require Import bitvector tactics list.

From SailStdpp Require Import MachineWord.

Import ListNotations.

From SailStdpp Require Import Values.

Local Open Scope list_scope.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Definition eqb {n} (v1 v2 : bv n) : bool :=
  v1.(bv_unsigned) =? v2.(bv_unsigned).
Definition ltb {n} (v1 v2 : bv n) : bool :=
  v1.(bv_unsigned) <? v2.(bv_unsigned).
Definition leb {n} (v1 v2 : bv n) : bool := 
  ltb v1 v2 || eqb v1 v2.
Definition gtb {n} (v1 v2 : bv n) : bool := 
  ltb v2 v1.
Definition geb {n} (v1 v2 : bv n) : bool := 
  gtb v1 v2 || eqb v1 v2.

Local Close Scope Z_scope.
Local Open Scope bv_scope.

Notation "x =? y" := (eqb x y) (at level 70, no associativity) : bv_scope.
Notation "x <? y" := (ltb x y) (at level 70, no associativity) : bv_scope.
Notation "x <=? y" := (leb x y) (at level 70, no associativity) : bv_scope.
Notation "x >? y" := (gtb x y) (at level 70, no associativity) : bv_scope.
Notation "x >=? y" := (geb x y) (at level 70, no associativity) : bv_scope.

Local Notation "(<@{ A } )" := (@lt A) (only parsing) : stdpp_scope.
Local Notation LtDecision A := (RelDecision (<@{A})).

(** Utility converters and lemmas **)

Definition bv_to_Z_unsigned {n} (v : bv n) : Z := v.(bv_unsigned).
Definition bv_to_N {n}  (v : bv n) : N := Z.to_N v.(bv_unsigned).
Definition bv_to_bv {n} {m : N} (v : bv n) : (bv m) :=
  Z_to_bv m (bv_to_Z_unsigned v).
Definition bv_to_list_bool {n} (v : bv n) : list bool := bv_to_bits v. 

Definition mword_to_bv {n} : mword n -> bv (N.of_nat (Z.to_nat n)) := 
  fun x => get_word x.

Definition bv_to_mword {n} : bv (N.of_nat (Z.to_nat n)) -> mword n :=
  match n with
  | Zneg _ => fun _ => MachineWord.zeros _
  | Z0 => fun w => w
  | Zpos _ => fun w => w
  end.
Definition bv_to_mword' {n} : bv (N.of_nat (Z.to_nat n)) -> mword n := 
  fun w => to_word w.
  
Definition invert_bits {n} (m : mword n) : (mword n) :=
  let l : list bool := mword_to_bools m in 
  let l := map negb l in 
  let x : mword (Z.of_nat (base.length l)) := of_bools l in
  let x : Z := int_of_mword false x in 
  mword_of_int x.

Lemma bv_eqb_eq {n} : forall (a b: bv n), (a =? b) = true <-> a = b.
Proof.
  split.
  - intro H. unfold eqb in H. 
    apply Z.eqb_eq in H. apply bv_eq in H. exact H.
  - intro H. rewrite H. unfold eqb. lia.
Defined.  

Lemma bv1_neqb_eq0 : forall (a : bv 1), (a =? 1%bv) = false <-> a = 0%bv.
Proof.
  intros. split.
  + intro H. unfold eqb in H. apply Z.eqb_neq in H. apply bv_eq.     
    assert (P: (0 ≤ bv_unsigned a < 2)%Z); [ apply (bv_unsigned_in_range 1 a) |].
    change (bv_unsigned 0) with 0%Z. change (bv_unsigned 1) with 1%Z in H. lia.
  + intro H. rewrite H. done.
Qed.

(** Inlike OCaml version if lists have different sizes, we just terminate
    after consuming the shortest one, without signaling error *)
Fixpoint fold_left2 {A B C:Type} (f: A -> B -> C -> A) (accu:A) (l1:list B) (l2:list C): A :=
  match l1, l2 with
  | a1::l1, a2::l2 => fold_left2 f (f accu a1 a2) l1 l2
  | _, _ => accu
  end.

Definition bool_list_cmp (a b: list bool) : bool :=
  if Nat.eqb (List.length a) (List.length b)
  then fold_left2 (fun a b c => andb (Bool.eqb b c) a) true a b
  else false.

Definition mem {A:Type} `{forall (x y:A), Decidable (x = y)} (a:A): (list A) -> bool
  := List.existsb (fun e => decide (e = a)).

Definition mapi {A B: Type} (f: nat -> A -> B) (l:list A) : list B :=
  let fix map_ n (l:list A) :=
    match l with
    | [] => []
    | a :: t => (f n a) :: (map_ (S n) t)
    end
  in map_ O l.

Definition maybeEqualBy
  {A: Type}
  (f: A -> A -> bool)
  (a: option A)
  (b: option A)
  : bool
  :=
  match a,b with
  | None, None => true
  | Some a, Some b => f a b
  | _, _ => false
  end.

Definition vector_drop {A:Type} {t:nat} (h:nat) (v:Vector.t A (h+t)) : Vector.t A t
  :=  snd (Vector.splitat h v).

Definition byte_of_Z (z:Z): ascii :=
  match z with
  | Z0 => Ascii.zero
  | Zpos x => ascii_of_pos x
  | Zneg _ =>
      let n := Z.abs_nat (Z.opp (Z.add z 1%Z)) in
      match ascii_of_nat n with
      | Ascii a1 a2 a3 a4 a5 a6 a7 a8 => Ascii (negb a1) (negb a2) (negb a3) (negb a4) (negb a5) (negb a6) (negb a7) true
      end
  end.

Definition bool_bits_of_bytes (bytes : list ascii): list bool
  :=
  let ascii_to_bits (x:ascii) :=
    match x with
    | Ascii a0 a1 a2 a3 a4 a5 a6 a7 => [a7; a6; a5; a4; a3; a2; a1; a0]
    end
  in
  List.concat (map ascii_to_bits bytes).

Lemma byte_chunks_len {a} (l : list a) l'  :
  (8 | length l)%nat → 
  byte_chunks l = Some l' → 
  length l' = ((length l)/8)%nat.
Proof.
  intro Hdiv. unfold Nat.divide in Hdiv. destruct Hdiv as [q Hdiv].

  assert (P: ∀ q (l : list a) l', length l = (q*8)%nat → byte_chunks l = Some l' → length l' = q).
  { intro q'. induction q' as [| n IH].
    { intros l0 l0' Hlen Hbytes. simpl in Hlen. apply nil_length_inv in Hlen. subst.
      simpl in Hbytes. injection Hbytes. intros. subst. done. }
    { intros l0 l0' Hlen Hbytes. unfold byte_chunks in Hbytes.
      destruct l0 eqn:E; [ done |].
      repeat case_match; try done. 
      assert (Hlensub: length l8 = (n*8)%nat).
      { repeat rewrite cons_length in Hlen. simpl in Hlen. lia. }
        specialize IH with (l:=l8) (l':=l9). 
        apply IH in Hlensub; [| done]. 
        injection Hbytes. intro H'.
        rewrite <- H'. rewrite cons_length. lia. } }
  
  intro Hbytes. specialize P with (l:=l). apply P; try done.
  rewrite Hdiv. rewrite Nat.div_mul; lia.    
  Qed.

(* could be generalized as monadic map, or implemented as composition
   of [map] and [sequence]. *)
Fixpoint try_map {A B:Type} (f : A -> option B) (l:list A) : option (list B)
  :=
  match l with
  | [] => Some []
  | a :: t =>
      match f a with
      | Some b =>
          match try_map f t with
          | Some bs =>  Some (b :: bs)
          | None => None
          end
      | None => None
      end
  end.

  Fact try_map_length
  {A B:Type}
  (f : A -> option B) (l:list A)
  (l':list B):
  try_map f l = Some l' -> length l = length l'.
Proof.
  intros H.
  revert l' H.
  induction l.
  - intros l' H.
    cbn in *.
    inversion H.
    reflexivity.
  - intros l' H.
    cbn in *.
    destruct (f a) eqn:Hfa; [| inversion H].
    destruct (try_map f l) eqn:Htry; [| inversion H].
    destruct l' as [| l0' l']; inversion H.
    subst.
    cbn.
    f_equal.
    apply IHl.
    reflexivity.
Qed.

Lemma try_map_to_map {A B:Type} (f : A -> option B) (l : list A) (l' : list B) : 
  try_map f l = Some l' ↔  
  map f l = map Some l'.
Proof. 
  revert l l'. 
  assert (H: ∀ n l l', length l = n → try_map f l = Some l' ↔ map f l = map Some l').
  { induction n as [| m IH].
    + intros l l' H_len. apply list.nil_length_inv in H_len. 
      subst. simpl. split; intro H. 
      - inversion H. subst. reflexivity.
      - symmetry in H. apply map_eq_nil in H. subst. reflexivity. 
    + intros l l' H_len. destruct l as [| h t ] eqn:H_l; [ done |].
      split; intro H; rewrite list.cons_length in H_len; apply eq_add_S in H_len.
      - simpl in H. case_match eqn:H_h; try done. case_match eqn:H_t; try done.
        match goal with 
        | _: try_map _ ?t = Some ?l
          |- _ 
            => apply (IH t l H_len) in H_t
        end.    
        simpl. inversion H as [H']. 
        rewrite H_h H_t. reflexivity.
      - simpl. simpl in H. 
        assert (H_len': length l' = S m). 
        { rewrite <- (map_length f) in H_len. rewrite <- H_len. 
          rewrite <- (cons_length (f h)). rewrite H. by rewrite map_length. }          
        destruct l' as [|h' t'] eqn:H_l'; [ done |].   
        case_match eqn:H_h; try done. case_match eqn:H_t. 
        * apply f_equal. subst. 
          apply (IH t) in H_t; try done. rewrite H_t in H. rewrite <- map_cons in H.
          by simplify_list_eq. 
        * subst. simpl in H. 
          apply (app_inj_2 [Some b] [Some h']) in H;
          [| rewrite !map_length; rewrite cons_length in H_len'; lia ].  
          destruct H as [_ H].
          apply (IH t) in H; [| reflexivity ]. rewrite H in H_t. done.  
  } 
  intros l l'. by apply (H (length l) l l').
Qed.

Lemma try_map_app {A B:Type} (f : A -> option B) (l1 l2 : list A) (l1' l2' : list B) : 
  try_map f (l1++l2)%list = Some (l1'++l2')%list →  
  length l1 = length l1' → 
  try_map f l1 = Some l1' ∧ try_map f l2 = Some l2'.
Proof.
  intros H_map H_len.
  apply try_map_to_map in H_map. rewrite !map_app in H_map.
  apply (list.app_inj_1) in H_map; [| by rewrite !map_length ]. 
  destruct H_map as [? ?].
  split; by apply try_map_to_map.
Qed.

Definition Z_integerRem_t := Z.rem.

Definition Z_integerRem_f a b :=
  let r := Z.rem a b in
  if Z.geb (Z.sgn r) 0 then r else Z.add r (Z.abs b).

Definition Z_integerDiv_t := Z.div.

Definition float_of_bits (_:Z): float := PrimFloat.zero. (* TODO: implement *)

Definition bits_of_float (_:float) : Z := Z.zero. (* TODO: implement *)

Fixpoint List_bool_eqb (l1:list bool) (l2:list bool) : bool := 
  match (l1,l2) with
    ([],[]) => true 
  | ([],_) => false 
  | (_,[]) => false 
  | (h1::t1,h2::t2) => (Bool.eqb h1 h2) && List_bool_eqb t1 t2
  end.
  
Definition string_of_bool (b:bool) :=
  match b with
  | true => "true"
  | false => "false"
  end.

Lemma ascii_eq_refl: forall x : ascii, Ascii.compare x x = Eq.
Proof.
  intros x.
  unfold compare.
  apply N.compare_eq_iff.
  reflexivity.
Qed.

Lemma string_eq_refl: forall x : string, String.compare x x = Eq.
Proof.
  intros x.
  induction x.
  - auto.
  - cbn.
    rewrite ascii_eq_refl.
    assumption.
Qed.

Lemma string_eq_trans: forall x y z : string,
    String.compare x y = Eq ->
    String.compare y z = Eq ->
    String.compare x z = Eq.
Proof.
  intros x y z H0 H1.
  apply String.compare_eq_iff in H0, H1.
  rewrite H0 H1.
  apply string_eq_refl.
Qed.

Lemma Z_eqb_is_eq (x y : Z) :
  (x =? y ↔ x = y)%Z.
Proof.
  split.
  + intros.
    apply Z.eqb_eq.
    by apply Is_true_eq_true.
  + intros ->.
    by rewrite Z.eqb_refl.
Qed.