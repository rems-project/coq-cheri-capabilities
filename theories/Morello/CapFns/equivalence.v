
Require Import Lia.

From SailStdpp Require Import Values Prompt_monad MachineWord.

From CheriCaps Require Import CapFns CapFnsTypes CapFns_Sail_gen CapFnsTypes_Sail_gen.
Require Import Coq.Program.Equality.


Definition M := CapFnsTypes_Sail_gen.M.

Definition CapGetTop_m := CapFns_Sail_gen.CapGetTop.
Definition CapGetTop_nm := CapFns.CapGetTop.

(* Definition CapGetBounds_short1_m := CapFns_Sail_gen.CapGetBounds_short1.
Definition CapGetBounds_short1_nm := CapFns.CapGetBounds_short1.
Definition CapGetBounds_short2_m := CapFns_Sail_gen.CapGetBounds_short2.
Definition CapGetBounds_short2_nm := CapFns.CapGetBounds_short2. *)

Definition CapGetBounds_m := CapFns_Sail_gen.CapGetBounds.
Definition CapGetBounds_nm := CapFns.CapGetBounds.

Definition CapBoundsEqual_m := CapFns_Sail_gen.CapBoundsEqual.
Definition CapBoundsEqual_nm := CapFns.CapBoundsEqual.

Definition CapIsRepresentable_m := CapFns_Sail_gen.CapIsRepresentable.
Definition CapIsRepresentable_nm := CapFns.CapIsRepresentable.


Lemma CAP_MAX_ENCODEABLE_EXPONENT_equiv : CapFns_Sail_gen.CAP_MAX_ENCODEABLE_EXPONENT = CapFns.CAP_MAX_ENCODEABLE_EXPONENT.
Proof. reflexivity. Qed.  

Lemma CAP_BOUND_MIN_equiv : CapFns_Sail_gen.CAP_BOUND_MIN = CapFns.CAP_BOUND_MIN.
Proof. reflexivity. Qed.  

Lemma CAP_BOUND_MAX_equiv : CapFns_Sail_gen.CAP_BOUND_MAX = CapFns.CAP_BOUND_MAX.
Proof. reflexivity. Qed.  

Lemma CAP_LIMIT_LO_BIT_equiv : CapFns_Sail_gen.CAP_LIMIT_LO_BIT = CapFns.CAP_LIMIT_LO_BIT.
Proof. reflexivity. Qed.  

Lemma CAP_LIMIT_HI_BIT_equiv : CapFns_Sail_gen.CAP_LIMIT_HI_BIT = CapFns.CAP_LIMIT_HI_BIT.
Proof. reflexivity. Qed.  

Lemma CAP_MAX_EXPONENT_equiv : CapFns_Sail_gen.CAP_MAX_EXPONENT = CapFns.CAP_MAX_EXPONENT.
Proof. reflexivity. Qed.  

Lemma CAP_MW_equiv : CapFns_Sail_gen.CAP_MW = CapFns.CAP_MW.
Proof. reflexivity. Qed. 

Lemma CapIsInternalExponent_equiv : 
  forall (c : mword 129),
  CapFns_Sail_gen.CapIsInternalExponent c = CapFns.CapIsInternalExponent c.
Proof. reflexivity. Qed.

Lemma returnDoneEqual {A} (x:A) : returnM x = Done x.
Proof. reflexivity. Qed.

(* Lemma returnmDoneEqual {A} {rv} (x:A) :
  returnm x = Done x.
Proof. reflexivity. Qed. *)

Lemma CapUnsignedLessThan_equiv {N} (a : mword N) (b : mword N) :
  CapFns_Sail_gen.CapUnsignedLessThan a b = CapFns.CapUnsignedLessThan a b.
Proof. reflexivity. Qed.

Lemma CapUnsignedGreaterThan_equiv {N : Z} (a : mword N) (b : mword N) : 
  CapFns_Sail_gen.CapUnsignedGreaterThan a b = CapFns.CapUnsignedGreaterThan a b.
Proof. reflexivity. Qed.

Lemma CapGetExponent_equiv (c : mword 129) :
  CapFns_Sail_gen.CapGetExponent c = CapFns.CapGetExponent c.
Proof. reflexivity. Qed.

Lemma CapIsExponentOutOfRange_equiv (c : mword 129) : 
  CapFns_Sail_gen.CapIsExponentOutOfRange c = CapFns.CapIsExponentOutOfRange c.
Proof. reflexivity. Qed.

Lemma CapGetBottom_equiv (c : mword 129) : 
  CapFns_Sail_gen.CapGetBottom c = CapFns.CapGetBottom c.
Proof. reflexivity. Qed.

Lemma CapGetValue_equiv (c : mword 129) : CapFns_Sail_gen.CapGetValue c = CapFns.CapGetValue c.
Proof. reflexivity. Qed.

Lemma CapBoundsAddress_equiv (address : mword (63 - 0 + 1)) : 
  CapFns_Sail_gen.CapBoundsAddress address = CapFns.CapBoundsAddress address.
Proof. reflexivity. Qed.

Lemma __id_equiv : CapFns_Sail_gen.__id = CapFns.__id.
Proof. reflexivity. Qed.

Lemma Zeros_equiv : CapFns_Sail_gen.Zeros = CapFns.Zeros.
Proof. reflexivity. Qed.

Ltac try_renaming :=
  try (change CapFns_Sail_gen.CAP_MAX_ENCODEABLE_EXPONENT with 63 in *);
  try (change CapFns.CAP_MAX_ENCODEABLE_EXPONENT with 63 in *);
  try (change CapFns_Sail_gen.CAP_MAX_EXPONENT with 50 in *);
  try (change CapFns.CAP_MAX_EXPONENT with 50 in *);
  try (rewrite CAP_BOUND_MIN_equiv in *);
  try (rewrite CAP_BOUND_MAX_equiv in *);
  try (rewrite CAP_LIMIT_LO_BIT_equiv in *);
  try (rewrite CAP_LIMIT_HI_BIT_equiv in *);
  try (rewrite CAP_MAX_EXPONENT_equiv in *);
  try (rewrite CAP_MW_equiv in *);
  try (rewrite CapIsInternalExponent_equiv in *);
  try (rewrite returnDoneEqual in *);
  try (rewrite CapUnsignedLessThan_equiv in *);
  try (rewrite CapUnsignedGreaterThan_equiv in *);
  try (rewrite CapGetExponent_equiv in *);
  try (rewrite CapIsExponentOutOfRange_equiv in *);
  try (rewrite CapGetBottom_equiv in *);
  try (rewrite CapGetValue_equiv in *);
  try (rewrite CapBoundsAddress_equiv in *);
  try (rewrite __id_equiv in *);
  try (rewrite Zeros_equiv in *);
  try (change (CapFns_Sail_gen.CAP_MW) with 16 in *);
  try (change (CapFns.CAP_MW) with 16 in *);
  try (change (CapFns_Sail_gen.CapUnsignedLessThan ?x ?y) with (CapUnsignedLessThan x y) in *);
  try (change (CapFns_Sail_gen.CapUnsignedGreaterThan ?x ?y) with (CapUnsignedGreaterThan x y) in *);
  try (change (CapFns_Sail_gen.Bit ?x) with (Bit x) in *).  

Lemma Choose_injective {rv A E} s ty (x y : choose_type ty -> monad rv A E) :
  (Choose s ty x = Choose s ty y)  ->  (x = y).
Proof. intros [=]. assumption. Qed.
  (* or intros. injection H. auto. Qed *)

Ltac CapGetTop_tac :=
  (* simpl; *) unfold CapGetTop; simpl; intros; try_renaming;
  destruct (CapIsInternalExponent _); reflexivity.

Theorem CapGetTop_equiv :
  forall (c : mword 129), 
    match (CapFns_Sail_gen.CapGetTop c) with 
      Choose _ ty f => 
        forall (v : choose_type ty),
          match (f v) with 
            Done result => result = (CapFns.CapGetTop c)
          | _ => False 
          end
      | _ => False
  end.
Proof. (*CapGetTop_tac. Qed.*) Admitted.

Fixpoint M_List_Returns {a} (opts : forall ty, list (choose_type ty)) (m : M a) := 
  match m with
  | Done v => List.cons v List.nil
  | Choose _ ty f => List.concat (List.map (fun x => M_List_Returns opts (f x)) (opts ty))
  | _ => List.nil
  end.

Inductive equiv {rv A E} : monad rv A E -> A -> Prop :=
| Finished : forall x y, x = y -> equiv (Done x) y
| Nondet : forall str ty f y, (forall x, equiv (f x) y) -> equiv (Choose str ty f) y
.

Fixpoint default_m {rv A E} (m : monad rv A E) dflt : A :=
  match m with
  | Done v => v
  | Choose _ ty f => default_m (f (TypeCasts.inhabitant)) dflt
  | _ => dflt
  end.

Theorem equiv_let_same :
  forall {A B rv E : Type} (y : A) (f : A -> monad rv B E) g,
  (forall x, equiv (f x) (g x)) ->
  equiv (let x := y in f x) (let x := y in g x).
Proof.
  intros.
  apply H.
Qed.

Theorem equiv_let_tuple2_same :
  forall {A B C rv E : Type} y1 y2 (f : A -> B -> monad rv C E) g,
  y1 = y2 ->
  (forall x1 x2, equiv (f x1 x2) (g x1 x2)) ->
  equiv (let '(x1, x2) := y1 in f x1 x2) (let '(x1, x2) := y2 in g x1 x2).
Proof.
  intros.
  rewrite H.
  destruct y2.
  apply H0.
Qed.

Theorem default_m_comm_let :
  forall {A B rv E : Type} (y : A) (f : A -> monad rv B E) dflt,
  default_m (let x := y in f x) dflt = (let x := y in default_m (f x) dflt).
Proof.
  auto.
Qed.

Theorem default_m_comm_let2 :
  forall {A B C rv E : Type} y (f : A -> B -> monad rv C E) dflt,
  default_m (let '(x1, x2) := y in f x1 x2) dflt = (let '(x1, x2) := y in default_m (f x1 x2) dflt).
Proof.
  intros.
  destruct y.
  auto.
Qed.

Theorem equiv_let_tuple2_prop :
  forall {A B} (P : (A * B) -> (A * B) -> Prop) {C rv E : Type} y1 y2 (f : A -> B -> monad rv C E) g,
  P y1 y2 ->
  (forall x11 x12 x21 x22, P (x11, x12) (x21, x22) -> equiv (f x11 x12) (g x21 x22)) ->
  equiv (let '(x1, x2) := y1 in f x1 x2) (let '(x1, x2) := y2 in g x1 x2).
Proof.
  intros.
  destruct y1.
  destruct y2.
  apply H0.
  auto.
Qed.

Theorem equiv_if :
  forall {A rv E : Type} P1 P2 (x1 : monad rv A E) x2 y1 y2,
  P1 = P2 ->
  (P1 = true -> equiv x1 x2) ->
  (P1 = false -> equiv y1 y2) ->
  equiv (if P1 then x1 else y1) (if P2 then x2 else y2).
Proof.
  intros.
  rewrite<- H.
  destruct P1; auto.
Qed.

(*
Theorem equiv_let_tuple2_default_same :
  forall {A B C rv E : Type} y1 y2 (f : A -> B -> monad rv C E) g,
  y1 = y2 ->
  (forall x1 x2, equiv (f x1 x2) (default_m (g x1 x2))) ->
  equiv (let '(x1, x2) := y1 in f x1 x2) (default_m (let '(x1, x2) := y2 in g x1 x2)).
Proof.
  intros.
  rewrite H.
  destruct y2.
  apply H0.
Qed.
*)

Theorem CapGetTop_equiv3 :
  forall (c : mword 129),
  equiv (CapFns_Sail_gen.CapGetTop c) (default_m (CapFns_Sail_gen.CapGetTop c) TypeCasts.inhabitant).
Proof.
  intros.
  unfold CapFns_Sail_gen.CapGetTop.
  cbn.
  apply Nondet.
  intros.
  repeat rewrite default_m_comm_let2.
  cbn.
  apply equiv_let_tuple2_same.
  auto.
  intros.
  apply Finished.
  auto.
Qed.

Theorem CapGetTop_equiv4 :
  forall (c : mword 129),
  equiv (CapFns_Sail_gen.CapGetTop c) (CapFns.CapGetTop c).
Proof.
  intros.
  unfold CapFns_Sail_gen.CapGetTop, CapFns.CapGetTop.
  cbn.
  apply Nondet.
  intros.
  apply equiv_let_tuple2_same.
  reflexivity.
  intros.
  apply Finished.
  rewrite CapGetBottom_equiv.
  rewrite CapUnsignedLessThan_equiv.
  reflexivity. 
Qed.

Theorem CapGetTop_equiv2 :
  forall (opts : forall ty, list (choose_type ty)) (c : mword 129),
  List.Forall (fun v => v = CapFns.CapGetTop c)
  (M_List_Returns opts (CapFns_Sail_gen.CapGetTop c)).
Proof.
  intros.
  destruct (CapFns_Sail_gen.CapGetTop c) eqn: e; pose (y := CapGetTop_equiv c); rewrite e in y; try tauto.
  cbn.
  rewrite Forall_concat.
  rewrite Forall_map.
  rewrite Forall_forall.
  intros.
  specialize y with x.
  destruct (m x); try tauto.
  cbn.
  apply Forall_cons; auto.
Qed.

Theorem CapGetBounds_equiv4 :
  forall (c : mword 129),
  equiv (CapFns_Sail_gen.CapGetBounds c) (CapFns.CapGetBounds c).
Proof.
  intros.
  unfold CapFns_Sail_gen.CapGetBounds, CapFns.CapGetBounds.
  apply equiv_if; intros.
      reflexivity.
    apply Finished.
    reflexivity.
  apply equiv_if; intros.
      reflexivity.
    apply Finished.
    reflexivity.

  apply Nondet.
  intros.
  apply Nondet.
  intros.
  try_renaming.
  
    Admitted.

Lemma resolve_bind_Done {A} {B} (g : B) : 
    bind (Done g)  
  =  
    (fun f : B -> monad register_value A unit => 
      f g).
Proof. simpl. reflexivity. Qed.

Lemma resolve_bind_Undefined_Bitvector {A} {n} (c : mword 129): 
    bind (Undefined.undefined_bitvector n) 
  = 
    (fun f : bits n -> monad register_value A unit =>
      (Choose "undefined_bitvector" 
        (ChooseBitvector n) 
        (fun (x : mword n) => f x))).  
Proof. simpl. reflexivity. Qed.    

Lemma resolve_bind_CapGetBounds {A} (c : mword 129)  : 
    bind (CapFns_Sail_gen.CapGetBounds c)  
  =  
    (fun f : (bits 65 * bits 65 * bool) -> monad register_value A unit =>
      f (CapFns.CapGetBounds c)).
Proof. Admitted.

(* Lemma resolve_bind_CapIsRepresentableFast {A} (c : mword 129) (v : mword 64)  : 
  bind (CapFns_Sail_gen.CapIsRepresentableFast c v)  
=  
  (fun f : bool -> monad register_value A unit =>
    f (CapFns.CapIsRepresentableFast c v)).
Proof. Admitted. *)

Lemma CapBoundsEqual_equiv : 
  forall (c1 c2 : mword 129),
    equiv (CapFns_Sail_gen.CapBoundsEqual c1 c2) (CapFns.CapBoundsEqual c1 c2).
Proof.
  intros. unfold CapFns_Sail_gen.CapBoundsEqual, CapFns.CapBoundsEqual.
  cbn.
  repeat (apply Nondet; intros).
  Admitted.

Lemma CapIsRepresentable_equiv : 
  forall (c : mword 129) (v : mword 64),
    equiv (CapFns_Sail_gen.CapIsRepresentable c v) (CapFns.CapIsRepresentable c v).
Proof.
  intros.
  unfold CapFns_Sail_gen.CapIsRepresentable, CapFns.CapIsRepresentable.
  apply CapBoundsEqual_equiv.
  Qed.

Lemma CapGetLength_equiv : 
  forall (c : mword 129),
    equiv (CapFns_Sail_gen.CapGetLength c) (CapFns.CapGetLength c).
Proof.
  intros.
  unfold CapFns_Sail_gen.CapGetLength, CapFns.CapGetLength.
  cbn.
  apply Nondet.
  intros. apply Nondet.
  intros. rewrite resolve_bind_CapGetBounds. apply equiv_let_tuple2_same; [ reflexivity |].
  intros. apply equiv_let_tuple2_same; [ reflexivity |]. 
  intros. apply Finished; reflexivity.
  Qed.

(* Lemma CapAdd_equiv : 
  forall (c : mword 129) (v : mword 64),
    equiv (CapFns_Sail_gen.CapAdd c v) (CapFns.CapAdd c v).
Proof.
  intros. unfold CapFns_Sail_gen.CapAdd, CapFns.CapAdd.
  rewrite resolve_bind_CapIsRepresentableFast.
  apply Finished.
  try_renaming.
  reflexivity.
Qed. *)

  
  (* CapSetValue

  CapIsRangeInBounds

  CapGetBase

  CapSetBounds

  CapGetRepresentableMask

  CapIsBaseAboveLimit

  CapIsSubSetOf

  CapIsInBounds

  CapSetOffset *)


(* Inductive Is_Deterministic_M {a} (m : M a) : Prop :=
  | DoneCase (x : match m with Done _ => True | _ => False end) : Is_Deterministic_M m
  | ChooseCase (x : match m with 
                    Choose _ ty f => forall (v : choose_type ty), Is_Deterministic_M (f v)
                  | _ => False end) : Is_Deterministic_M m. *)