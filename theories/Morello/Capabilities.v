Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.HexString.
Require Import Coq.ZArith.Zdigits.

From stdpp.unstable Require Import bitvector bitvector_tactics bitblast. 

From SailStdpp Require Import Base Values Values_lemmas Operators_mwords MachineWord Operators_mwords MachineWordInterface.

From CheriCaps.Common Require Import Utils Addr Capabilities.
From CheriCaps Require Import CapFns.


(** Notations and their definitions **)

Definition eqb {n} (v1 v2 : bv n) : bool :=
  v1.(bv_unsigned) =? v2.(bv_unsigned).
Definition ltb {n} (v1 v2 : bv n) : bool :=
  v1.(bv_unsigned) <? v2.(bv_unsigned).
Definition leb {n} (v1 v2 : bv n) : bool := 
  ltb v1 v2 || eqb v1 v2.
Definition gtb {n} (v1 v2 : bv n) : bool := 
  leb v2 v1.
Definition geb {n} (v1 v2 : bv n) : bool := 
  gtb v1 v2 || eqb v1 v2.

Local Close Scope Z_scope.
Local Open Scope bv_scope.

Local Notation "x =? y" := (eqb x y) (at level 70, no associativity) : bv_scope.
Local Notation "x <? y" := (ltb x y) (at level 70, no associativity) : bv_scope.
Local Notation "x <=? y" := (leb x y) (at level 70, no associativity) : bv_scope.
Local Notation "x >? y" := (gtb x y) (at level 70, no associativity) : bv_scope.
Local Notation "x >=? y" := (geb x y) (at level 70, no associativity) : bv_scope.

Local Notation "(<@{ A } )" := (@lt A) (only parsing) : stdpp_scope.
Local Notation LtDecision A := (RelDecision (<@{A})).

(** Utility converters **)

Definition bv_to_Z_unsigned {n} (v : bv n) : Z := v.(bv_unsigned).
Definition bv_to_N {n}  (v : bv n) : N := Z.to_N v.(bv_unsigned).
Definition bv_to_bv {n} {m : N} (v : bv n) : (bv m) :=
  Z_to_bv m (bv_to_Z_unsigned v).
Definition bv_to_list_bool {n} (v : bv n) : list bool := bv_to_bits v. 

Definition mword_to_bv {n} : mword n -> bv (N.of_nat (Z.to_nat n)) := 
  fun x => get_word x.

Definition bv_to_mword {n} : bv (N.of_nat (Z.to_nat n)) -> mword n :=
  match n with
  | Zneg _ => fun _ => zeros _
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


Module Permissions <: PERMISSIONS.
  Definition len:N := 18. (* CAP_PERMS_NUM_BITS = 16 bits of actual perms + 2 bits for Executive and Global *)
  Definition t := bv len.
    
  Definition to_Z (perms:t) : Z := bv_to_Z_unsigned perms.
  Definition of_Z (z:Z) : t := Z_to_bv len z.
  
  (* Higher indexes in the list encode the most-significant permission bits (eg, l[17] encodes Load permission) *)
  Program Definition of_list_bool (l:list bool) `{(N.of_nat (List.length l) = len)%N} : t := 
    MachineWord.N_to_word (List.length l) (Ascii.N_of_digits l).
  Next Obligation. auto. Defined.
  
  Definition user_perms_len:nat := 4.

  Variant perm := Load_perm | Store_perm | Execute_perm | LoadCap_perm | StoreCap_perm | StoreLocalCap_perm | Seal_perm | Unseal_perm
  | System_perm | BranchSealedPair_perm | CompartmentID_perm | MutableLoad_perm | User1_perm | User2_perm | User3_perm | User4_perm | Executive_perm | Global_perm.

  Definition has_perm (permissions:t) : _ -> bool :=
    let permissions : (mword (Z.of_N len)) := permissions in 
    let perms : (mword 64) := zero_extend permissions 64 in 
    fun perm => CapPermsInclude perms perm.

  Definition has_global_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_GLOBAL.
  Definition has_executive_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_EXECUTIVE.
  Definition has_execute_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_EXECUTE.
  Definition has_load_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_LOAD.
  Definition has_load_cap_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_LOAD_CAP.
  Definition has_seal_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_SEAL.
  Definition has_store_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_STORE.
  Definition has_store_cap_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_STORE_CAP.
  Definition has_store_local_cap_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_STORE_LOCAL.
  Definition has_system_access_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_SYSTEM.
  Definition has_unseal_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_UNSEAL.
  Definition has_user1_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_USER1.
  Definition has_user2_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_USER2.
  Definition has_user3_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_USER3.
  Definition has_user4_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_USER4.
  Definition has_compartmentID_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_COMPARTMENT_ID.
  Definition has_branch_sealed_pair_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_BRANCH_SEALED_PAIR.
  Definition has_ccall_perm (permissions:t) : bool := 
    has_branch_sealed_pair_perm permissions.
  Definition has_mutable_load_perm (permissions:t) : bool := 
    has_perm permissions CAP_PERM_MUTABLE_LOAD.
          
  Definition get_user_perms (permissions:t) : list bool := 
    [ has_user1_perm permissions; has_user2_perm permissions; 
      has_user3_perm permissions; has_user4_perm permissions ]. 

  (* Returns true iff all permissions in perms2 are also in perms1. *)
  Fixpoint includes (perms1 : t) (perms2 : list perm) : bool :=  
    match perms2 with
    | []                        => true 
    | Load_perm::tl             => has_load_perm perms1 && includes perms1 tl 
    | Store_perm::tl            => has_store_perm perms1 && includes perms1 tl 
    | Execute_perm::tl          => has_execute_perm perms1 && includes perms1 tl 
    | LoadCap_perm ::tl         => has_load_cap_perm perms1 && includes perms1 tl 
    | StoreCap_perm::tl         => has_store_cap_perm perms1 && includes perms1 tl 
    | StoreLocalCap_perm::tl    => has_store_local_cap_perm perms1 && includes perms1 tl 
    | Seal_perm::tl             => has_seal_perm perms1 && includes perms1 tl 
    | Unseal_perm::tl           => has_unseal_perm perms1 && includes perms1 tl 
    | System_perm::tl           => has_system_access_perm perms1 && includes perms1 tl 
    | BranchSealedPair_perm::tl => has_branch_sealed_pair_perm perms1 && includes perms1 tl 
    | CompartmentID_perm::tl    => has_compartmentID_perm perms1 && includes perms1 tl 
    | MutableLoad_perm::tl      => has_mutable_load_perm perms1 && includes perms1 tl 
    | User1_perm::tl            => has_user1_perm perms1 && includes perms1 tl 
    | User2_perm::tl            => has_user2_perm perms1 && includes perms1 tl 
    | User3_perm::tl            => has_user3_perm perms1 && includes perms1 tl 
    | User4_perm::tl            => has_user4_perm perms1 && includes perms1 tl 
    | Executive_perm::tl        => has_executive_perm perms1 && includes perms1 tl 
    | Global_perm::tl           => has_global_perm perms1 && includes perms1 tl 
    end.

  Definition list_perm_to_list_bool (perms: list perm) : list bool :=  
    let isLoad_perm : (perm -> bool) := fun p => match p with Load_perm => true | _ => false end in 
    let isStore_perm : (perm -> bool) := fun p => match p with Store_perm => true | _ => false end in 
    let isExecute_perm : (perm -> bool) := fun p => match p with Execute_perm => true | _ => false end in 
    let isLoadCap_perm : (perm -> bool) := fun p => match p with LoadCap_perm => true | _ => false end in 
    let isStoreCap_perm : (perm -> bool) := fun p => match p with StoreCap_perm => true | _ => false end in 
    let isStoreLocalCap_perm : (perm -> bool) := fun p => match p with StoreLocalCap_perm => true | _ => false end in 
    let isSeal_perm : (perm -> bool) := fun p => match p with Seal_perm => true | _ => false end in 
    let isUnseal_perm : (perm -> bool) := fun p => match p with Unseal_perm => true | _ => false end in 
    let isSystem_perm : (perm -> bool) := fun p => match p with System_perm => true | _ => false end in 
    let isBranchSealedPair_perm : (perm -> bool) := fun p => match p with BranchSealedPair_perm => true | _ => false end in 
    let isCompartmentID_perm : (perm -> bool) := fun p => match p with CompartmentID_perm => true | _ => false end in 
    let isMutableLoad_perm : (perm -> bool) := fun p => match p with MutableLoad_perm => true | _ => false end in 
    let isUser1_perm : (perm -> bool) := fun p => match p with User1_perm => true | _ => false end in 
    let isUser2_perm : (perm -> bool) := fun p => match p with User2_perm => true | _ => false end in 
    let isUser3_perm : (perm -> bool) := fun p => match p with User3_perm => true | _ => false end in 
    let isUser4_perm : (perm -> bool) := fun p => match p with User4_perm => true | _ => false end in 
    let isExecutive_perm : (perm -> bool) := fun p => match p with Executive_perm => true | _ => false end in 
    let isGlobal_perm : (perm -> bool) := fun p => match p with Global_perm => true | _ => false end in 
      [ existsb (isGlobal_perm) perms;           existsb (isExecutive_perm) perms; 
        existsb (isUser1_perm) perms;            existsb (isUser2_perm) perms;  
        existsb (isUser3_perm) perms;            existsb (isUser4_perm) perms;   
        existsb (isMutableLoad_perm) perms;      existsb (isCompartmentID_perm) perms; 
        existsb (isBranchSealedPair_perm) perms; existsb (isSystem_perm) perms;    
        existsb (isUnseal_perm) perms;           existsb (isSeal_perm) perms;     
        existsb (isStoreLocalCap_perm) perms;    existsb (isStoreCap_perm) perms; 
        existsb (isLoadCap_perm) perms;          existsb (isExecute_perm) perms;  
        existsb (isStore_perm) perms;            existsb (isLoad_perm) perms  ].

  Program Definition make_permissions (perms: list perm) : t :=  
    @of_list_bool (list_perm_to_list_bool perms) _.
    Next Obligation. auto. Defined.

  Program Definition perm_and_user_perms (perms:t) (user_perms:list bool) : t := 
    let user_perm_4 := (nth 3 user_perms false) && (has_user4_perm perms) in   
    let user_perm_3 := (nth 2 user_perms false) && (has_user3_perm perms) in 
    let user_perm_2 := (nth 1 user_perms false) && (has_user2_perm perms) in 
    let user_perm_1 := (nth 0 user_perms false) && (has_user1_perm perms) in 
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; 
    user_perm_1; user_perm_2; user_perm_3; user_perm_4; has_mutable_load_perm perms;
    has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms;
    has_unseal_perm perms; has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms;
    has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms; has_load_perm perms ] _.
   Next Obligation. reflexivity. Defined.
      
  Program Definition perm_p0 : t := 
    @of_list_bool (list_perm_to_list_bool []) _.
   Next Obligation. reflexivity. Defined.

  Definition perm_Universal : t := 
    (make_permissions [ Global_perm; Executive_perm; User1_perm; User2_perm; 
    User3_perm; User4_perm; MutableLoad_perm; CompartmentID_perm; BranchSealedPair_perm; 
    System_perm; Unseal_perm; Seal_perm; StoreLocalCap_perm; StoreCap_perm; LoadCap_perm; 
    Execute_perm; Store_perm; Load_perm ]).
    
  Definition perm_alloc : t :=
    (make_permissions [ Load_perm; Store_perm; LoadCap_perm; StoreCap_perm; StoreLocalCap_perm ]).
    
  Definition perm_alloc_fun : t := 
    (make_permissions [ Load_perm; Execute_perm; LoadCap_perm ]).
    
  Program Definition perm_clear_global (perms:t) : t :=
    @of_list_bool [ false; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.

  Program Definition perm_clear_executive (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; false; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms;
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.
    
  Program Definition perm_clear_execute (perms:t) : t :=
   @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
   has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
   has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; false; has_store_perm perms;
   has_load_perm perms ] _.
   Next Obligation. reflexivity. Defined.
 
  Program Definition perm_clear_load (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    false ] _.
    Next Obligation. reflexivity. Defined.
  
  Program Definition perm_clear_load_cap (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; false; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.
  
  Program Definition perm_clear_seal (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    false; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.
  
  Program Definition perm_clear_store (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; false;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.  

  Program Definition perm_clear_store_cap (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; false; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.

  Program Definition perm_clear_store_local_cap (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; false; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.

  Program Definition perm_clear_system_access (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; false; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.

  Program Definition perm_clear_unseal (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; false;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.

  Program Definition perm_clear_branch_sealed_pair (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; false; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.

  Program Definition perm_clear_ccall (perms:t) : t := 
    perm_clear_branch_sealed_pair perms.  

  Program Definition perm_clear_mutable_load (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    false; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.  

  Program Definition perm_clear_compartment_ID (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms; 
    has_mutable_load_perm perms; false; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.  

  Program Definition perm_clear_user1 (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; false; has_user2_perm perms; has_user3_perm perms; has_user4_perm perms;  
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.    

  Program Definition perm_clear_user2 (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; false; has_user3_perm perms; has_user4_perm perms;
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.  

  Program Definition perm_clear_user3 (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; false; has_user4_perm perms; 
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.  

  Program Definition perm_clear_user4 (perms:t) : t :=
    @of_list_bool [ has_global_perm perms; has_executive_perm perms; has_user1_perm perms; has_user2_perm perms; has_user3_perm perms; false;
    has_mutable_load_perm perms; has_compartmentID_perm perms; has_branch_sealed_pair_perm perms; has_system_access_perm perms; has_unseal_perm perms;
    has_seal_perm perms; has_store_local_cap_perm perms; has_store_cap_perm perms; has_load_cap_perm perms; has_execute_perm perms; has_store_perm perms;
    has_load_perm perms ] _.
    Next Obligation. reflexivity. Defined.  
  
  Definition to_string (perms:t) : string :=
      let s (f:bool) l := if f then l else "" in
      s (has_load_perm perms) "r"
      ++ s (has_store_perm perms) "w"
      ++ s (has_execute_perm perms) "x"
      ++ s (has_load_cap_perm perms) "R"
      ++ s (has_store_cap_perm perms) "W"
      ++ s (has_executive_perm perms) "E".

  Definition to_string_hex (perms:t) : string :=      
    HexString.of_Z (bv_to_Z_unsigned perms). 

  Definition to_raw (perms:t) : Z := bv_to_Z_unsigned perms.

  Definition of_list (l : list bool) : option t := 
    if ((List.length l) <? (N.to_nat len))%nat then
      None 
    else
      Some (@mword_to_bv (Z.of_N len) (of_bools (List.rev (List.firstn (N.to_nat len) l)))).
  
  Definition to_list (perms:t) : list bool := 
    bv_to_list_bool perms.

  Definition eqb (a b:t) : bool := eqb a b.

End Permissions.


Module AddressValue <: PTRADDR.

  Definition len:N := 64.
  Definition t := bv len.

  Definition of_Z (z:Z) : t := Z_to_bv len z.
  Definition to_Z (v:t) : Z := bv_to_Z_unsigned v.
  Definition with_offset (v:t) (o:Z) : t :=
    of_Z (to_Z v + o).

  Definition bitwise_complement_Z (a:Z) : Z :=
    let bits := Z_to_binary (N.to_nat len) a in
    let bits := Vector.map negb bits in
    binary_value _ bits.

  Definition bitwise_complement (a:t) : t :=
    of_Z (bitwise_complement_Z (to_Z a)).

  Definition eqb (v1:t) (v2:t) : bool := Capabilities.eqb v1 v2.
  Definition ltb (v1:t) (v2:t) : bool := Capabilities.ltb v1 v2.
  Definition leb (v1:t) (v2:t) : bool := Capabilities.leb v1 v2.

  Definition to_string (v:t) : string := HexString.of_Z (bv_to_Z_unsigned v).
  
  Definition ltb_irref: forall a:t, ltb a a = false.
  Proof. intros. unfold ltb. unfold Capabilities.ltb. rewrite Z.ltb_irrefl. reflexivity. Qed. 

  Global Instance morello_address_eq_dec : EqDecision t.
  Proof. unfold t. apply bv_eq_dec. Defined.
  
  Global Instance morello_address_countable : countable.Countable t.
  Proof. unfold t. apply bv_countable. Defined.

End AddressValue.


Module ObjType <: OTYPE.

  Definition len:N := 64.
  Definition t := bv len.  (* ObtTypes are effectively 15-bit values,
  but the ASL extracts this field from a cap as a 64-bit word, 
  possibly to match the size of the objTypes stored in sealing caps *)

  (* Definition CAP_OTYPE_LO_BIT:N := 95.
  Definition CAP_OTYPE_HI_BIT:N := 109.
  Definition CAP_OTYPE_NUM_BITS:N := 15. *)
  Definition CAP_MAX_OBJECT_TYPE:N := 32767.

  Definition of_Z (z:Z) : t := Z_to_bv len z.
  Definition to_Z (o:t) : Z := bv_to_Z_unsigned o.

  Definition eqb (a b:t) : bool := eqb a b.

End ObjType.


Module SealType <: CAP_SEAL_T.

  Inductive cap_seal_t :=
  | Cap_Unsealed
  | Cap_SEntry (* "RB" in Morello *)
  | Cap_Indirect_SEntry (* "LB" in Morello *)
  | Cap_Indirect_SEntry_Pair (* "LPB" in Morello *)
  | Cap_Sealed (seal : ObjType.t).
  
  Definition t := cap_seal_t. 

  Definition get_seal_ot (seal:t) : ObjType.t :=
    match seal with 
      Cap_Unsealed => ObjType.of_Z 0
    | Cap_SEntry => ObjType.of_Z 1
    | Cap_Indirect_SEntry => ObjType.of_Z 3
    | Cap_Indirect_SEntry_Pair => ObjType.of_Z 2
    | Cap_Sealed seal => seal
    end.

  Definition sealed_entry_ot := get_seal_ot Cap_SEntry.
  Definition sealed_indirect_entry_ot := get_seal_ot Cap_Indirect_SEntry.
  Definition sealed_indirect_entry_pair_ot := get_seal_ot Cap_Indirect_SEntry_Pair.

  Definition eqb (a b: t) :=
    match a, b with
    | Cap_Unsealed, Cap_Unsealed => true
    | Cap_SEntry, Cap_SEntry => true
    | Cap_Indirect_SEntry, Cap_Indirect_SEntry => true
    | Cap_Sealed a, Cap_Sealed b => ObjType.eqb a b
    | _, _ => false
    end.

End SealType.


Module Flags <: FLAGS.

  Definition length:nat := 8.
  Definition t := { l : list bool | List.length l = length }.
  Definition eqb (f1:t) (f2:t) : bool := List_bool_eqb (proj1_sig f1) (proj1_sig f2).

End Flags.


Module Bounds <: PTRADDR_INTERVAL(AddressValue).

  Definition bound_len:N := 65.
  Definition t := ((bv bound_len) * (bv bound_len))%type.
  Definition CAP_MAX_LIMIT_BOUND := (2^64)%Z.
  
  Definition of_Zs (bounds : Z * Z) : t :=
    let '(base,limit) := bounds in   
    (Z_to_bv bound_len base, Z_to_bv bound_len limit). 
  
  Definition of_addresses (a b : AddressValue.t) : t := 
    of_Zs (AddressValue.to_Z a, AddressValue.to_Z b).

  Definition to_Zs (bounds : t) : Z * Z :=
    let (base,top) := bounds in   
    (bv_to_Z_unsigned base, bv_to_Z_unsigned top).
  
  Definition address_is_in_interval (bounds:t) (value:AddressValue.t) : bool :=
    let '(base,limit) := bounds in 
    let value : (bv bound_len) := bv_to_bv value in 
    (base <=? value) && (value <? limit).

  Definition ltb (a b:t) := 
    let '(base_a, limit_a) := a in
    let '(base_b, limit_b) := b in
    ((base_a <? base_b) && (limit_a <=? limit_b))
    || ((base_a <=? base_b) && (limit_a <? limit_b)).

  Definition contained (a b:t) := 
    let '(base_a, limit_a) := a in
    let '(base_b, limit_b) := b in
    (base_a >=? base_b) && (limit_a <=? limit_b).

  Definition to_string (b:t) : string := 
    let (base,top) := b in 
    HexString.of_Z (bv_to_Z_unsigned base) ++ "-" ++ HexString.of_Z (bv_to_Z_unsigned top).

  Definition eqb (a b:t) : bool :=
    let (a0,a1) := a in
    let (b0,b1) := b in
    eqb a0 b0 && eqb a1 b1.

End Bounds. 


Module Capability <: CAPABILITY (AddressValue) (Flags) (ObjType) (SealType) (Bounds) (Permissions).
  Definition len:N := 129.
  Definition t := bv len.
  
  Definition of_Z (z:Z) : t := Z_to_bv len z.

  Definition of_bvn (b:bvn) (tag:bool) : option t := 
    if (b.(bvn_n) =? (len-1))%N then 
      let bits : (list bool) := tag::(bools_of_int (Z.of_N len-1) b.(bvn_val).(bv_unsigned)) in
      let bitsu := List.map bitU_of_bool bits in
      let w : (mword _) := vec_of_bits bitsu in
      let z : Z := int_of_mword false w in 
      let c : option t := Z_to_bv_checked len z in 
      match c with 
        Some c => Some c
      | None   => None
      end
    else 
      None.
     
  Definition cap_SEAL_TYPE_UNSEALED : ObjType.t := ObjType.of_Z 0.
  Definition cap_SEAL_TYPE_RB : ObjType.t := ObjType.of_Z 1. 
  Definition cap_SEAL_TYPE_LPB : ObjType.t := ObjType.of_Z 2. 
  Definition cap_SEAL_TYPE_LB : ObjType.t := ObjType.of_Z 3.

  Definition sizeof_ptraddr := 8%nat. (* in bytes *)
  (* Definition ptraddr_bits := sizeof_ptraddr * 8. *)
  Definition min_ptraddr := Z_to_bv (N.of_nat (sizeof_ptraddr*8)) 0.  
  Definition max_ptraddr := Z_to_bv (N.of_nat (sizeof_ptraddr*8)) (Z.sub (bv_modulus (N.of_nat (sizeof_ptraddr*8))) 1).

  Definition cap_c0 (u:unit) : t := CapNull u.

  Definition cap_cU (u:unit) : t := concat_vec (Ones 19) (Zeros 110).

  Definition bound_null (u:unit) : bv 65 := Z_to_bv 65 0.

  Definition cap_get_value (c:t) : AddressValue.t := CapGetValue c.
  
  Definition cap_get_obj_type (c:t) : ObjType.t := CapGetObjectType c.

  Definition cap_get_bounds_ (c:t) : Bounds.t * bool :=
    let '(base_mw, limit_mw, isExponentValid) := CapGetBounds c in
    let base_bv := base_mw in
    let limit_bv := limit_mw in 
    ((base_bv, limit_bv), isExponentValid).
  
  Definition cap_get_bounds (cap:t) : Bounds.t :=
    let '(base_mw, limit_mw, isExponentValid) := 
      cap_get_bounds_ cap in
    (base_mw, limit_mw).

  (* Returns the bounds as pairs of AddressValues, but if the limit bound is the maximum 
  bound (the only valid bound value that cannot be represented as an AddressValue) it just returns both bounds as 0. *)
  Definition cap_get_bounds_adrs (cap:t) : AddressValue.t * AddressValue.t :=
    let (base,limit) := cap_get_bounds cap in 
    if (limit.(bv_unsigned) =? Bounds.CAP_MAX_LIMIT_BOUND)%Z then
      (AddressValue.of_Z 0, AddressValue.of_Z 0)
    else 
      let (base',limit') := Bounds.to_Zs (base,limit) in 
      (AddressValue.of_Z base', AddressValue.of_Z limit').
  
  Definition cap_get_offset (c:t) : Z := (CapGetOffset c).(bv_unsigned).
    
  Definition cap_get_seal (cap:t) : SealType.t := 
    let ot:ObjType.t := cap_get_obj_type cap in
    if (ot =? cap_SEAL_TYPE_UNSEALED) then SealType.Cap_Unsealed else
    if (ot =? cap_SEAL_TYPE_RB) then SealType.Cap_SEntry else
    if (ot =? cap_SEAL_TYPE_LPB) then SealType.Cap_Indirect_SEntry_Pair else 
    if (ot =? cap_SEAL_TYPE_LB) then SealType.Cap_Indirect_SEntry else 
    SealType.Cap_Sealed ot.
    
  (* The flags are the top byte of the value. *)
  Program Definition cap_get_flags (c:t) : Flags.t := 
    let c : (mword (Z.of_N len)) := c in
    let m : (mword _) := subrange_vec_dec c CAP_VALUE_HI_BIT CAP_FLAGS_LO_BIT in
    let l : (list bool) := List.rev (mword_to_bools m) in
    exist _ l _.
  Next Obligation. reflexivity. Defined.  

  Definition cap_get_perms (c:t) : Permissions.t := CapGetPermissions c.

  Definition cap_is_sealed (c:t) : bool := CapIsSealed c.
  
  Definition cap_invalidate (c:t) : t := CapWithTagClear c.

  Definition cap_set_value (c:t) (value:AddressValue.t) : t :=
    let new_cap := CapSetValue c value in 
    if (cap_is_sealed c) then (cap_invalidate new_cap) else new_cap.
  
  Definition cap_add_offset_to_value (c:t) (o:Z) : t :=
    cap_set_value c (AddressValue.with_offset (cap_get_value c) o).
  
  Definition cap_set_flags (c:t) (f: Flags.t) : t :=
    let new_cap :=
      let flags_m : (mword (Z.of_nat Flags.length)) := of_bools (List.rev (proj1_sig f)) in
      let flags' : (mword 64) := concat_vec flags_m (Zeros (64 - (Z.of_nat Flags.length))) in 
       CapSetFlags c flags' in 
    if (cap_is_sealed c) then (cap_invalidate new_cap) else new_cap.
  
  Definition cap_set_objtype (c:t) (ot:ObjType.t) : t :=
    let ot : (mword (Z.of_N ObjType.len)) := ot in 
    CapSetObjectType c (zero_extend ot 64).

  (* [perms] must contain [1] for permissions to be kept and [0] for those to be cleared *)
  Definition cap_narrow_perms (c:t) (perms:Permissions.t) : t :=
    let perms_mw : (mword (Z.of_N Permissions.len)) := perms in 
    let mask : (mword 64) := zero_extend perms_mw 64 in
    let mask_inv : (mword 64) := invert_bits mask in 
    let new_cap := CapClearPerms c mask_inv in 
    if (cap_is_sealed c) then (cap_invalidate new_cap) else new_cap.

  Definition cap_clear_global_perm (cap:t) : t :=     
    cap_narrow_perms cap (Permissions.perm_clear_global (cap_get_perms cap)).
    
  Definition cap_set_bounds (c : t) (bounds : Bounds.t) (exact : bool) : t :=
    (* CapSetBounds sets the lower bound to the value of the input cap,
       so we first have to set the value of cap to bounds.base. *)
    let '(base,limit) := bounds in
    let base_as_val : AddressValue.t := bv_to_bv base in  
    let new_cap := cap_set_value c base_as_val in 
    let req_len : (mword (Z.of_N Bounds.bound_len)) := 
      mword_of_int (Z.sub (bv_to_Z_unsigned limit) (bv_to_Z_unsigned base)) in 
    let new_cap := CapSetBounds new_cap req_len exact in 
    if (cap_is_sealed c) then (cap_invalidate new_cap) else new_cap.

  Definition cap_narrow_bounds (cap : t) (bounds : Bounds.t) : t :=
    cap_set_bounds cap bounds false.

  Definition cap_narrow_bounds_exact (cap : t) (bounds : Bounds.t) : t :=
    cap_set_bounds cap bounds true.

  Definition cap_get_all_addresses_in_bounds (cap : t) : list AddressValue.t := 
    let (base,limit) := Bounds.to_Zs (cap_get_bounds cap) in 
    let addresses : list nat := List.seq (Z.to_nat base) (Z.to_nat limit - Z.to_nat base) in 
    map AddressValue.of_Z (map Z.of_nat addresses).

  Definition bounds_contained (c1 c2 : t) : bool :=
    Bounds.contained (cap_get_bounds c1) (cap_get_bounds c2).    
  
  Definition cap_is_valid (cap:t) : bool := Bool.eqb (CapIsTagClear cap) false.

  Definition cap_is_invalid (cap:t) : bool := negb (cap_is_valid cap).
    
  Definition cap_is_unsealed (cap:t) : bool := negb (cap_is_sealed cap).
  
  Definition cap_is_in_bounds (cap:t) : bool := CapIsInBounds cap.

  Definition cap_is_not_in_bounds (cap:t) : bool := negb (cap_is_in_bounds cap).  
  
  Definition cap_is_exponent_out_of_range (cap:t) : bool := CapIsExponentOutOfRange cap.

  Definition cap_has_no_permissions (cap:t) : bool := 
    ((cap_get_perms cap).(bv_unsigned) =? (Permissions.perm_p0).(bv_unsigned))%Z.

  Definition cap_has_empty_bounds (cap:t) : bool := 
    let (base,limit) := cap_get_bounds cap in 
    (limit.(bv_unsigned) <=? base.(bv_unsigned))%Z.

  Definition cap_permits_system_access (cap:t) : bool := 
    Permissions.has_system_access_perm (cap_get_perms cap).
  
  Definition cap_permits_seal (cap:t) : bool := 
    Permissions.has_seal_perm (cap_get_perms cap).
  
  Definition cap_permits_unseal (cap:t) : bool := 
    Permissions.has_unseal_perm (cap_get_perms cap).
  
  Definition cap_permits_store (cap:t) : bool := 
    Permissions.has_store_perm (cap_get_perms cap).
  
  Definition cap_permits_store_cap (cap:t) : bool := 
    Permissions.has_store_cap_perm (cap_get_perms cap).
  
  Definition cap_permits_store_local_cap (cap:t) : bool := 
    Permissions.has_store_local_cap_perm (cap_get_perms cap).
  
  Definition cap_permits_load (cap:t) : bool := 
    Permissions.has_load_perm (cap_get_perms cap).
  
  Definition cap_permits_load_cap (cap:t) : bool := 
    Permissions.has_load_cap_perm (cap_get_perms cap).
  
  Definition cap_permits_execute (cap:t) : bool := 
    Permissions.has_execute_perm (cap_get_perms cap).
  
  Definition cap_permits_ccall (cap:t) : bool := 
    Permissions.has_ccall_perm (cap_get_perms cap).

  Definition cap_is_global (cap:t) : bool :=
    Permissions.has_global_perm (cap_get_perms cap).

  Definition cap_permits (cap:t) (perms : list Permissions.perm) : bool := 
    Permissions.includes (cap_get_perms cap) perms.

  Definition leq_perms (c1 c2 : t) : bool :=
    if (cap_is_global c1) && negb (cap_is_global c2) then false
    else if (cap_permits_execute c1) && negb (cap_permits_execute c2) then false
    else if (cap_permits_ccall c1) && negb (cap_permits_ccall c2) then false
    else if (cap_permits_load c1) && negb (cap_permits_load c2) then false
    else if (cap_permits_load_cap c1) && negb (cap_permits_load_cap c2) then false
    else if (cap_permits_seal c1) && negb (cap_permits_seal c2) then false
    else if (cap_permits_unseal c1) && negb (cap_permits_unseal c2) then false
    else if (cap_permits_store c1) && negb (cap_permits_store c2) then false
    else if (cap_permits_store_cap c1) && negb (cap_permits_store_cap c2) then false
    else if (cap_permits_store_local_cap c1) && negb (cap_permits_store_local_cap c2) then false
    else if (cap_permits_system_access c1) && negb (cap_permits_system_access c2) then false
    else true.
  
  Definition cap_seal (cap : t) (k : t) : t :=
    let key : ObjType.t := cap_get_value k in 
    let sealed_cap := cap_set_objtype cap key in 
    if (cap_is_valid cap) && (cap_is_valid k) && 
       (cap_is_unsealed cap) && (cap_is_unsealed k) && 
       (cap_permits_seal k) && (cap_is_in_bounds k) &&
       (Z.to_N (bv_to_Z_unsigned key) <=? ObjType.CAP_MAX_OBJECT_TYPE)%N then 
       sealed_cap
    else
       cap_invalidate sealed_cap.

  Definition cap_unseal_direct (sealed_cap:t) : t := CapUnseal sealed_cap.

  Definition cap_unseal (sealed_cap:t) (unsealing_cap:t) : t :=
    let value := cap_get_value unsealing_cap in 
    let key := cap_get_obj_type sealed_cap in 
    let unsealed_sealed_cap := 
      cap_unseal_direct sealed_cap in 
    let unsealed_sealed_cap := 
      if (negb (cap_is_global unsealing_cap)) then
        cap_clear_global_perm unsealed_sealed_cap
      else unsealed_sealed_cap in 
    if (cap_is_valid sealed_cap && cap_is_valid unsealing_cap 
        && cap_is_sealed sealed_cap && cap_is_unsealed unsealing_cap
        && cap_permits_unseal unsealing_cap
        && cap_is_in_bounds unsealing_cap && (key =? value)) then 
      unsealed_sealed_cap
    else 
      cap_invalidate unsealed_sealed_cap.

  Definition cap_seal_immediate (cap : t) (seal_ot : ObjType.t) 
    `{ArithFact ((bv_to_Z_unsigned seal_ot >? 0)%Z && (bv_to_Z_unsigned seal_ot <=? 4)%Z)} : t :=
    let new_cap := cap_set_objtype cap seal_ot in 
    if (cap_is_valid cap && cap_is_unsealed cap) then 
      new_cap
    else
      cap_invalidate new_cap.

  (* For sealing with RB *)
  Definition cap_seal_entry (cap:t) : t := cap_seal_immediate cap SealType.sealed_entry_ot.

  (* For sealing with LB *)
  Definition cap_seal_indirect_entry (cap:t) : t := 
    cap_seal_immediate cap SealType.sealed_indirect_entry_ot.

  (* For sealing with LPB *)  
  Definition cap_seal_indirect_entry_pair (cap:t) : t := 
    cap_seal_immediate cap SealType.sealed_indirect_entry_pair_ot.

  Definition representable_alignment_mask (len:Z) : Z :=
    uint (CapGetRepresentableMask (mword_of_int len)).

  Definition representable_length (len : Z) : Z :=
    let mask:Z := representable_alignment_mask len in
    let nmask:Z := AddressValue.bitwise_complement_Z mask in
    let result:Z := Z.land (Z.add len nmask) mask in 
      result.

  Definition make_cap (value : AddressValue.t) (otype : ObjType.t) (bounds : Bounds.t) (perms_to_keep : Permissions.t) : t :=
    let new_cap := cap_cU () in 
    let new_cap := cap_narrow_perms new_cap perms_to_keep in 
    let new_cap := cap_narrow_bounds new_cap bounds in 
    let new_cap := cap_set_value new_cap value in 
      cap_set_objtype new_cap otype.

  Definition alloc_cap (a_value : AddressValue.t) (size : AddressValue.t) : t :=
    make_cap 
      a_value 
      cap_SEAL_TYPE_UNSEALED 
      (Bounds.of_Zs (bv_to_Z_unsigned a_value, Z.add (bv_to_Z_unsigned a_value) (bv_to_Z_unsigned size)))
      (Permissions.perm_alloc).
    
  Definition alloc_fun (a_value : AddressValue.t) : t :=
    make_cap 
      a_value 
      cap_SEAL_TYPE_RB 
      (Bounds.of_Zs (bv_to_Z_unsigned a_value, Z.succ (Z.succ (bv_to_Z_unsigned a_value)))) 
      Permissions.perm_alloc_fun.

  Definition value_compare (cap1 cap2 : t) : comparison :=
    if (cap_get_value cap1 =? cap_get_value cap2) then Eq
    else if (cap_get_value cap1 <? cap_get_value cap2) then Lt
    else Gt.

  Definition exact_compare (cap1 cap2 : t) : comparison :=
    if (cap1 =? cap2) then Eq 
    else if (cap1 <? cap2) then Lt 
    else Gt.

  Definition cap_ptraddr_representable (c : t) (a : AddressValue.t) : bool :=
    CapIsRepresentable c a.
  
  Definition cap_bounds_representable_exactly (cap : t) (bounds : Bounds.t) : bool :=
    let '(base, limit) := bounds in
    let len := Z.sub (bv_to_Z_unsigned limit) (bv_to_Z_unsigned base) in
    let base' : (bv AddressValue.len) := 
      Z_to_bv AddressValue.len (bv_to_Z_unsigned base) in 
    let len' := mword_of_int (len:=Z.of_N Bounds.bound_len) len in 
    let new_cap : t := cap_set_value cap base' in
    let new_cap : (mword _) := CapSetBounds new_cap len' true in
    CapIsTagSet new_cap.

  Definition cap_bounds_check (cap:t) (bounds : Bounds.t) : bool :=
    let '(base, limit) := bounds in
    let len := Z.sub (bv_to_Z_unsigned limit) (bv_to_Z_unsigned base) in
    let base' : (bv AddressValue.len) := 
      AddressValue.of_Z (bv_to_Z_unsigned base) in 
    let len' := mword_of_int (len:=Z.of_N Bounds.bound_len) len in 
    CapIsRangeInBounds cap base' len'.

  Definition cap_is_null_derived (c : t) : bool :=
    let a := cap_get_value c in
    let c0 := cap_c0 () in
    let c' := cap_set_value c0 a in
    c =? c'.
    
  Definition bool_bits_of_bytes (bytes : list ascii): list bool
  :=
  let ascii_to_bits (x:ascii) :=
    match x with
    | Ascii a0 a1 a2 a3 a4 a5 a6 a7 => [a7; a6; a5; a4; a3; a2; a1; a0]
    end
  in
  List.fold_left (fun l a => List.app l (ascii_to_bits a)) bytes [].  

  (* Internal helper function to convert between Sail bytes ([memory_byte])
     and [ascii]. *)
  Definition memory_byte_to_ascii (b:memory_byte) : option ascii :=
    match List.map bool_of_bit b with
    | [a1;a2;a3;a4;a5;a6;a7;a8] => Some (Ascii a8 a7 a6 a5 a4 a3 a2 a1)
    | _ => None
    end.

  Fixpoint try_map {A B:Type} (f : A -> option B) (l:list A) : option (list B) :=
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

  Definition encode (isexact : bool) (c : t) : option ((list ascii) * bool) :=
    let tag : bool := cap_is_valid c in 
    let c : (mword (Z.of_N len)) := c in  (* why does Z.of_N len need to be specified? *)
    let cap_bits := bits_of c in 
    let w : (mword _) := vec_of_bits (List.tail cap_bits) in
    match mem_bytes_of_bits w with
    | Some bytes =>
        match try_map memory_byte_to_ascii bytes with
        | Some chars => Some (chars, tag)
        | None => None
        end
    | None => None
    end.

  Definition decode (bytes : list ascii) (tag : bool) : option t :=
    if Nat.eq_dec (List.length bytes) 16%nat then
      let bytes := List.rev bytes in (* TODO: bypassing rev could make this more efficient *)
      let bits : (list bool) := tag::(bool_bits_of_bytes bytes) in
      let bitsu := List.map bitU_of_bool bits in
      let w : (mword _) := vec_of_bits bitsu in
      (* Some (mword_to_bv w) *) (* This requires the proof below, but makes tests harder *)
      let z : Z := uint w in 
      let c : option t := Z_to_bv_checked len z in 
      match c with 
        Some c => Some c
      | None   => None
      end
    else
      None.
    (* Next Obligation.      
      intros. assert (P: length bytes = 16%nat).
      - unfold bytes. rewrite rev_length. apply e.
      - assert (Q: length (bool_bits_of_bytes bytes) = 128%nat).
        + assert (X: forall (bs:list ascii), length (bool_bits_of_bytes bs) = (8 * (length bs))%nat).
          { induction bs as [| h tl HInd].
          - reflexivity.
          - simpl bool_bits_of_bytes. rewrite app_length. destruct h.
            simpl length. rewrite HInd. 
            assert (T: (8 + 8 * base.length tl)%nat = (8*1 + 8 * base.length tl)%nat).
            + reflexivity.
            + rewrite T. rewrite <- mult_plus_distr_l. reflexivity. }
          rewrite X. rewrite P. reflexivity.
          + assert (R: length bits = 129%nat). 
            -- unfold bits. rewrite list.cons_length. rewrite Q. reflexivity. 
            -- unfold bitsu. unfold length_list. rewrite map_length. rewrite R. reflexivity.
    Defined. *)  

  Definition eqb_cap (cap1:t) (cap2:t) : bool := cap1 =? cap2.

  Definition eqb (cap1:t) (cap2:t) : bool := eqb_cap cap1 cap2.

  Definition is_sentry (c:t) : bool :=
    match cap_get_seal c with
    | SealType.Cap_SEntry => true
    | _                   => false
    end.

  Definition is_indirect_sentry (c:t) : bool :=
    match cap_get_seal c with
    | SealType.Cap_Indirect_SEntry      => true
    | SealType.Cap_Indirect_SEntry_Pair => true
    | _                                 => false
    end.
    
  Definition get_indirect_sentry_type (c:t) : option SealType.t :=
    match cap_get_seal c with
    | SealType.Cap_Indirect_SEntry      => Some SealType.Cap_Indirect_SEntry
    | SealType.Cap_Indirect_SEntry_Pair => Some SealType.Cap_Indirect_SEntry_Pair
    | _                                 => None 
    end.

  Definition flags_as_str (c:t): string :=
    let attrs : list string :=
      let a (f:bool) s l := if f then s::l else l in
        (a (negb (cap_is_valid c))) "invalid"
          (a (is_sentry c) "sentry"
            (a ((negb (is_sentry c)) && cap_is_sealed c) "sealed" []))
      in
    if Nat.eqb (List.length attrs) 0%nat then ""
    else " (" ++ String.concat "," attrs ++ ")".

  Definition to_string_pretty (c:t) : string :=
    AddressValue.to_string (cap_get_value c) ++ " [" ++ Permissions.to_string (cap_get_perms c) ++ "," ++ Bounds.to_string (cap_get_bounds c) ++ "]".

  Definition to_string_pretty_2 (c:t) : string :=
    if cap_is_null_derived c then
      AddressValue.to_string (cap_get_value c)
    else
      (AddressValue.to_string (cap_get_value c)) ++ " " ++ "[" ++
        ( Permissions.to_string (cap_get_perms c) ++ "," ++
          Bounds.to_string (cap_get_bounds c) )
        ++ "]" ++
        (flags_as_str c).

  Definition to_string_full (c:t) : string := HexString.of_Z (bv_to_Z_unsigned c). 

  Definition to_string (c:t) : string := to_string_pretty_2 c.

  Definition strfcap (s:string) (_:t) : option string := None.
    
  (* Could also implement a prettier to_string that produces something like
    { valid: yes
      value: 0xF...1
      base: 0xF...
      limit: ...
      seal: RB
      permissions: Load,Store,Execute
      flags: 10010...  
    }   *)  

  (* Lemma for eqb on capabilities directly without the ghoststate record.
  Lemma eqb_value_compare: forall a b, eqb a b = true -> value_compare a b = Eq.
  Proof. intros. unfold eqb in H. assert (P: a = b).
    { unfold eq in H. 
        rewrite -> Z.eqb_eq in H. 
        apply bv_eq. 
        apply H. }
        rewrite <- P. unfold value_compare. unfold eq. rewrite Z.eqb_refl. reflexivity. Qed. *)  

  Lemma eqb_value_compare: forall (a b : t), eqb a b = true -> value_compare a b = Eq.
  Proof. intros. unfold eqb in H. assert (P: a = b). (* or just apply Lemma eqb_cap_value_compare *)
    { unfold eqb_cap in H. unfold Capabilities.eqb in H. rewrite -> Z.eqb_eq in H. 
      apply bv_eq. apply H. }
    unfold value_compare. unfold cap_get_value.
    rewrite <- P. unfold Capabilities.eqb.
    rewrite Z.eqb_refl. reflexivity. Qed.
    
  (* Lemma for eqb on capabilities directly without the ghoststate record.
  Lemma eqb_exact_compare: forall a b, eqb a b = true <-> exact_compare a b = Eq.
  Proof. split.
    - unfold eqb. unfold exact_compare. intros. rewrite H. reflexivity. 
    - unfold eqb. unfold exact_compare. destruct (a =? b).
      + reflexivity.
      + destruct (b >? a). 
        { discriminate. } { discriminate. }
    Qed. *)

  Lemma eqb_exact_compare: forall (a b : t), eqb a b = true <-> exact_compare a b = Eq.
  Proof. split.
    - unfold eqb. unfold eqb_cap. unfold exact_compare. intros. rewrite H. reflexivity. 
    - unfold eqb. unfold eqb_cap. unfold exact_compare. destruct (a =? b).
      + reflexivity.
      + destruct (a <? b); discriminate.
    Qed.
        
  Lemma eqb_refl: forall (a:t), eqb a a = true.
  Proof.
    intros. unfold eqb; unfold eqb_cap; unfold Capabilities.eqb. apply Z.eqb_eq. reflexivity.
  Qed.

  Lemma eqb_eq : forall (a b:t), (a =? b) = true <-> a = b.
  Proof.
    split.
    - intro H. unfold Capabilities.eqb in H. 
      apply Z.eqb_eq in H. apply bv_eq in H. exact H.
    - intro H. rewrite H. apply eqb_refl.
  Defined.  
  
  Lemma cap_invalidate_invalidates (c:t) : cap_is_valid (cap_invalidate c) = false.
  Proof.
    unfold cap_invalidate, cap_is_valid.
    rewrite eqb_false_iff, not_false_iff_true.
    unfold CapIsTagClear, CapWithTagClear.
    rewrite eq_vec_true_iff.    
    unfold CapGetTag, CapSetTag, CAP_TAG_BIT.     
    change (Bit (vec_of_bits [access_vec_dec _ 0])) with B0.    
    unfold update_vec_dec, access_vec_dec, access_mword_dec.
    simpl (get_word _). 
    unfold MachineWord.set_bit, MachineWord.get_bit, MachineWord.update_slice, MachineWord.slice, MachineWord.zero_extend.
    bv_simplify.
    bitblast.
  Qed.

  Lemma cap_invalidate_preserves_value (c:t) : cap_get_value c = cap_get_value (cap_invalidate c).
  Proof.
    unfold cap_get_value, cap_invalidate, CapGetValue, CapWithTagClear, CapSetTag, CAP_VALUE_HI_BIT, CAP_VALUE_LO_BIT, CAP_TAG_BIT.
    unfold subrange_vec_dec, autocast. simpl. bv_simplify.
    change (Z.to_nat 0) with 0%nat.
    change (Z.to_nat 64) with 64%nat.
    change (Pos.to_nat 1) with 1%nat. 
    unfold MachineWord.slice, MachineWord.zero_extend, MachineWord.N_to_word. simpl.
    apply f_equal. 
    change (N.of_nat 0) with 0%N.
    change (N.of_nat 64) with 64%N.
    change (N.of_nat 1) with 1%N.
    change (Bit (vec_of_bits [access_vec_dec _ 0])) with B0.
    unfold update_vec_dec, update_mword_dec. simpl. 
    change (Z.to_nat 128) with 128%nat.
    unfold MachineWord.set_bit, MachineWord.update_slice, MachineWord.slice. simpl.
    change (N.of_nat (Z.to_nat 129)) with 129%N.
    change (N.of_nat 129) with 129%N.
    change (N.of_nat 0) with 0%N.
    change (N.of_nat 1) with 1%N.
    change (N.of_nat 128) with 128%N.
    replace (bool_to_bv 1 false) with (bv_0 1); [| vm_compute; bv_solve].
    replace (bv_extract _ 0 _) with (bv_0 0); [| bv_simplify; bitblast].
    bv_simplify.    
    rewrite bv_zero_extend_idemp.
    change (bv_zero_extend _ _) with (bv_concat 129 (bv_0 1) (bv_extract 0 128 c)).
    replace (bv_extract _ _ (bv_concat _ _ _)) with (bv_extract 0 64 (bv_extract 0 128 c)); [| bv_simplify; reflexivity].
    replace (bv_extract _ _ (bv_extract _ _ _)) with (bv_extract 0 64 c); [| bv_simplify; rewrite bv_extract_0_unsigned; rewrite bv_extract_0_unsigned; bv_simplify; reflexivity]. 
    reflexivity.
    Qed.

  Lemma subrange_vec_dec_after_clear_tag (c:t) (hi lo : Z) :
    let c : mword 129 := c in
    (hi <? 128)%Z -> (lo <? hi)%Z ->
    subrange_vec_dec c hi lo = subrange_vec_dec (CapWithTagClear c) hi lo.
  Proof.
    intros x H J. 
    assert (Hp: (hi < 128)%Z); [ apply Is_true_eq_true in H; lia |].
    unfold subrange_vec_dec, CapWithTagClear, CapSetTag, CAP_TAG_BIT, autocast. 
    simpl. bv_simplify.
    destruct (Z.eq_dec _ _); [| reflexivity].
    unfold MachineWord.slice, MachineWord.zero_extend, MachineWord.N_to_word. simpl.
    change (Bit (vec_of_bits [access_vec_dec _ 0])) with B0.
    unfold update_vec_dec, update_mword_dec. simpl. 
    unfold MachineWord.set_bit, MachineWord.update_slice, MachineWord.slice. simpl.
    replace (bv_extract _ 0 _) with (bv_0 0); [| bv_simplify; bitblast].
    bv_simplify.    
    rewrite bv_zero_extend_idemp.
    change (bv_zero_extend _ _) with (bv_concat 129 (bv_0 1) (bv_extract 0 128 c)).
    replace (N.of_nat (Z.to_nat lo)) with (Z.to_N lo); [| rewrite Z_nat_N; reflexivity].
    replace (bv_extract _ _ (bv_concat _ _ _)) with (bv_extract (Z.to_N lo) (N.of_nat (Z.to_nat hi - Z.to_nat lo + 1)) (bv_extract 0 128 c)); [| bv_simplify; reflexivity].
    set (len := (N.of_nat (Z.to_nat hi - Z.to_nat lo + 1))).
    replace (bv_extract _ _ (bv_extract _ _ _)) with (bv_extract (Z.to_N lo) len c). reflexivity.
    bv_simplify. rewrite bv_extract_unsigned. rewrite bv_extract_unsigned. bv_simplify.  bitblast.       
    Qed.  

  Lemma cap_invalidate_preserves_bounds (c:t) : cap_get_bounds c = cap_get_bounds (cap_invalidate c).
  Proof.
      Admitted.
  
End Capability.  


Module ExampleCaps.

  (* c1 corresponds to https://www.morello-project.org/capinfo?c=1900000007f1cff1500000000ffffff15 *)
  Definition c1:Capability.t := Capability.of_Z 0x1900000007f1cff1500000000ffffff15.
  Definition c1_bytes : list ascii := List.map ascii_of_nat (List.map Z.to_nat 
    [0x15;0xff;0xff;0xff;0;0;0;0;0x15;0xff;0x1c;0x7f;0;0;0;0x90]%Z).
  
  (* c2 corresponds to https://www.morello-project.org/capinfo?c=1d800000066f4e6ec00000000ffffe6ec *)
  Definition c2:Capability.t := Capability.of_Z 0x1d800000066f4e6ec00000000ffffe6ec.
  Definition c2_bytes : list ascii := List.map ascii_of_nat (List.map Z.to_nat (
    List.rev [0xd8;0x00;0x00;0x00;0x66;0xf4;0xe6;0xec;0x00;0x00;0x00;0x00;0xff;0xff;0xe6;0xec]%Z)).

  (* c3 corresponds to https://www.morello-project.org/capinfo?c=1dc00000066d4e6d02a000000ffffe6d0 *)
  Definition c3_bytes := ["208"%char;"230"%char;"255"%char;"255"%char;"000"%char;"000"%char;"000"%char;
    "042"%char;"208"%char;"230"%char;"212"%char;"102"%char;"000"%char;"000"%char;"000"%char;"220"%char].
  
End ExampleCaps.
