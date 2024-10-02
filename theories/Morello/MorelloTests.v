Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.HexString.

From stdpp.unstable Require Import bitvector bitvector_tactics. 
From stdpp Require Import bitvector.
From SailStdpp Require Import Values Operators_mwords.

From CheriCaps.Common Require Import Utils Addr Capabilities.
From CheriCaps.Morello Require Import CapFns.
From CheriCaps.Morello Require Export Capabilities.

Module test_cap_getters_and_setters.

  Import Capability.

  Definition c1:Capability.t := concat_vec (Ones 19) (Zeros 110). (* A valid universal-permission cap = 1^{19}0^{110} *)
  Definition c2:Capability.t := concat_vec (Ones 3) (Zeros 126).  (* A valid cap with Load and Store perms *)
  Definition c3:Capability.t := Capability.of_Z 0x1fc000000333711170000000012342222. (* The default cap on https://www.morello-project.org/capinfo *)
  Definition c4:Capability.t := Capability.of_Z 0x1fc000000399700070000000012342222. (* The bounds in this cap subsume those of c3 *)
  Definition c5:Capability.t := Capability.of_Z 0x1fb000000377700070011111111113333. (* Cap breakdown: https://www.morello-project.org/capinfo?c=0x1%3Afb00000037770007%3A0011111111113333 *)
  Definition c6:Capability.t := Capability.of_Z 0x1fb0000007a4700000000000000003333. (* Cap breakdown: https://www.morello-project.org/capinfo?c=0x1%3Afb0000007a470000%3A0000000000003333 *)
  Definition c7:Capability.t := Capability.of_Z 0x14C0000007F1CFF1500000000FFFFFF15.
  Definition c8:Capability.t := Capability.of_Z 0x1900000007f1cff1500000000ffffff15.
  Definition c9:Capability.t := Capability.of_Z 0x1ffffb000000000000000000000000000. (* Cap breakdown: https://www.morello-project.org/capinfo?c=0x1ffffb000000000000000000000000000 *)
  
  Program Definition flags1:Flags.t := exist _ [false; false; false; false; false; false; false; false] _. 
    Next Obligation. reflexivity. Defined.
  Program Definition flags2:Flags.t := exist _ [false; true; false; true; false; true; false; true] _. 
    Next Obligation. reflexivity. Defined.
    
  Definition perm_Load : Permissions.t := Permissions.make_permissions [Permissions.Load_perm].
  Definition perm_Load_Store : Permissions.t := Permissions.make_permissions [Permissions.Load_perm; Permissions.Store_perm].
  Definition perm_Load_Execute : Permissions.t := Permissions.make_permissions [Permissions.Load_perm; Permissions.Execute_perm].
  
  Example of_bvn_test_1 : 
    let drop_tag c : mword 128 := of_bools (List.tail (List.rev (bv_to_bits c))) in
    let drop_tag_bvn c := bv_to_bvn (drop_tag c) in
    of_bvn (drop_tag_bvn c1) true = Some c1 /\ of_bvn (drop_tag_bvn c2) true = Some c2 /\ of_bvn (drop_tag_bvn c3) true = Some c3 /\ of_bvn (drop_tag_bvn c4) true = Some c4 /\ of_bvn (drop_tag_bvn c5) true = Some c5 /\ of_bvn (drop_tag_bvn c6) true = Some c6 /\ of_bvn (drop_tag_bvn c7) true = Some c7 /\ of_bvn (drop_tag_bvn c8) true = Some c8.
  Proof. repeat (try split; try vm_compute; try (apply f_equal); try bv_solve). Qed.

  Example is_valid_test_1 : cap_is_valid c1 = true.
    Proof. reflexivity. Qed.

  Example is_valid_test_2 : cap_is_valid (cap_c0 ()) = false.
    Proof. reflexivity. Qed.

  Example is_valid_test_3 : cap_is_valid c5 = true.
    Proof. reflexivity. Qed.

  Example is_valid_test_4 : cap_is_valid c2 = true.
    Proof. reflexivity. Qed.

  Example value_test_1 : 
    let value:AddressValue.t := AddressValue.of_Z 5 in
    value = cap_get_value (cap_set_value c1 value).
    Proof. vm_compute. bv_solve. (*apply bv_eq. reflexivity. *) Qed. 

  Example flags_test_1 : flags1 = cap_get_flags c1.
    Proof. unfold flags1. unfold cap_get_flags. reflexivity. Qed.

  Example flags_test_2 : flags2 = cap_get_flags (cap_set_flags c1 flags2).
    Proof. vm_compute. reflexivity. Qed. 
  
  Import Permissions.
  
  Example permissions_test_1 : Permissions.perm_Universal = cap_get_perms c1.
    Proof. vm_compute. bv_solve. Qed.

  Example permissions_test_2 : perm_Load_Store = cap_get_perms c2.
    Proof. vm_compute. bv_solve. Qed.

  Example permissions_test_3 : 
    let mask : t := inv perm_Load_Store in
    perm_Load_Store = cap_get_perms (cap_narrow_perms c1 mask).
    Proof. vm_compute. bv_solve. Qed.

  Example permissions_test_4 : 
    let mask : t := inv perm_Load_Store in
    let cap := cap_narrow_perms c1 mask in 
    let mask : t := inv perm_Load_Execute in
    perm_Load = cap_get_perms (cap_narrow_perms cap mask).
    Proof. vm_compute. bv_solve. Qed.

  Example permissions_test_5 : 
    let mask1 : t := make_permissions [Load_perm; LoadCap_perm; Execute_perm; MutableLoad_perm; User1_perm; User2_perm; Seal_perm; CompartmentID_perm; Executive_perm] in  
    let mask2 : t := make_permissions [Store_perm; StoreCap_perm; StoreLocalCap_perm; System_perm; User3_perm; User4_perm; Unseal_perm; BranchSealedPair_perm; Global_perm] in 
    mask1 = inv mask2.
    Proof. vm_compute. bv_solve. Qed.
      
  Example permissions_test_6 : 
    let perms := cap_get_perms (cap_narrow_perms c1 (make_permissions [Global_perm])) in 
    perms = cap_get_perms c9 ∧ perms ≠ cap_get_perms c1.
    Proof. vm_compute. split. bv_solve. discriminate. Qed.    

  Example permissions_test_7 : 
    Permissions.of_Z (Permissions.to_Z perm_Load_Store) = perm_Load_Store.
    Proof. reflexivity. Qed.

  Example permissions_test_8 : 
    let cheri_perms_and (c:Capability.t) (mask:bv 64) : Capability.t := 
      let tag : bv 1 := bv_extract 128 1 c in
      let perms : bv 18 := bv_extract 110 18 c in 
      let rem : bv 110 := bv_extract 0 110 c in
      bv_concat 129 (bv_concat 19 tag (bv_and perms (bv_extract 0 18 mask))) rem in 
    let store_perms : bv 18 := make_permissions [Store_perm; StoreCap_perm; StoreLocalCap_perm] in 
    let store_mask : bv 64 := bv_not (bv_zero_extend 64 store_perms) in
    bv_to_Z_unsigned store_mask = 0xfffffffffffecfff ∧ 
    store_perms = bv_not (bv_extract 0 18 (Z_to_bv 64 0xfffffffffffecfff)) ∧ 
    Capability.cap_narrow_perms c1 store_perms = cheri_perms_and c1 store_mask.
    Proof. vm_compute. repeat split; bv_solve. Qed.

  Example permissions_test_9 : 
    let store_and_mask : list bool := [true; true; true; true; true; true; true; true; true; true; true; true; false; false; true; true; false; true; true; true; true; true; 
    true; true; true; true; true; true; true; true; true; true; true;
    true; true; true; true; true; true; true; true; true; true; true;
    true; true; true; true; true; true; true; true; true; true; true;
    true; true; true; true; true; true; true; true; true] in
    let store_perms := list.take 18 store_and_mask in 
    let store_perms := List.map negb store_perms in     
    match (Permissions.of_list store_perms) with 
    | Some perms => 
        let new_cap := Capability.cap_narrow_perms c1 perms in 
        Capability.cap_permits_store c1 = true ∧ Capability.cap_permits_store_cap c1 = true ∧ Capability.cap_permits_store_local_cap c1 = true ∧ 
        Capability.cap_permits_store new_cap = false ∧ Capability.cap_permits_store_cap new_cap = false ∧ Capability.cap_permits_store_local_cap new_cap = false ∧ 
        Permissions.to_string (Capability.cap_get_perms new_cap) = "rxRE"
    | None => False
    end.
  Proof. vm_compute. tauto. Qed.
    
  Example get_and_user_perms_test_1 : 
    let user_perms_A : (list bool) := get_user_perms (cap_get_perms (cap_cU ())) in 
    let user_perms_A := [ nth 0 user_perms_A false; negb (nth 1 user_perms_A false);
                        nth 2 user_perms_A false; negb (nth 3 user_perms_A false) ] in 
    let user_perms_B : Permissions.t := 
      perm_and_user_perms (cap_get_perms (cap_cU ())) user_perms_A in
      user_perms_A = [true; false; true; false] /\
      get_user_perms user_perms_B = user_perms_A.
    Proof. vm_compute. split. reflexivity. reflexivity. Qed. 
 
  Example eqb_and_narrow_perm_test_1 :
    let mask : Permissions.t := inv perm_Load_Store in
    (c2 = (cap_narrow_perms c1 mask))%stdpp.
    Proof. vm_compute. reflexivity. Qed.

  Example bounds_representable_exactly_test_1 :
    let bounds : Bounds.t := 
      (Z_to_bv Bounds.bound_len 305402128, Z_to_bv Bounds.bound_len 305427248) in (* the bounds of c3, which we know is representable *) 
    cap_bounds_representable_exactly c4 bounds = true.
    Proof. reflexivity. Qed. 
      
  Example bounds_representable_exactly_test_2 :
    let bounds : Bounds.t := 
      (Z_to_bv Bounds.bound_len 305402128, Z_to_bv Bounds.bound_len 306427248) in (* now we changed the common part of the bounds *) 
    cap_bounds_representable_exactly c4 bounds = false.
    Proof. reflexivity. Qed. 
  
  Example narrow_exact_and_get_bounds_test_1 : 
    (* The bounds of capability c5 are         (0x0011111111110000, 0x00011111111117770). *)
    let '(new_base,new_limit) := Bounds.of_Zs  (0x0011111111113330, 0x00011111111117440) in 
    (* We can see new_bounds can be represented exactly from cap5: https://www.morello-project.org/capinfo?c=0x1%3Afb00000034473337%3A1011111111113333 *)
    let new_cap := cap_narrow_bounds_exact c5 (new_base,new_limit) in 
    let result := cap_get_bounds new_cap in 
    (cap_is_valid c5) = true ∧ (cap_is_valid new_cap) = true
    ∧ cap_get_bounds_ new_cap = (new_base,new_limit,true).
    Proof. vm_compute. split. reflexivity. split. reflexivity. reflexivity. Qed. 
  
  Example seal_and_unseal_test_1 :
    (* c6 has Seal and Unseal permissions and its value is <= the largest objtype. *) 
    let sealed_cap := cap_seal c3 c6 in
    let unsealed_sealed_cap := cap_unseal sealed_cap c6 in 
    (cap_is_valid sealed_cap) = true /\ (cap_is_sealed sealed_cap) = true 
    /\ (cap_get_obj_type sealed_cap) = (cap_get_value c6) 
    /\ (cap_is_valid unsealed_sealed_cap) = true /\ (cap_is_unsealed unsealed_sealed_cap) = true.
    Proof. vm_compute. repeat ( split; try reflexivity; try bv_solve ). Qed.

  Example seal_entry_test_1 : 
    let sealed_cap := cap_seal_entry c4 in 
    let sealed_sealed_cap := cap_seal_entry sealed_cap in 
    let sealed_invalid_cap := cap_seal_entry (cap_invalidate c4) in 
    (cap_is_sealed sealed_cap) = true /\ (cap_is_valid sealed_cap) = true 
    /\ (cap_get_obj_type sealed_cap = SealType.sealed_entry_ot)
    /\ (cap_is_invalid sealed_sealed_cap) = true /\ (cap_is_invalid sealed_invalid_cap) = true.
    Proof. repeat ( split; try reflexivity ). Qed. 

  Example seal_indirect_entry_test_1 : 
    let sealed_cap := cap_seal_indirect_entry c3 in 
    let sealed_sealed_cap := cap_seal_indirect_entry sealed_cap in 
    let sealed_invalid_cap := cap_seal_indirect_entry (cap_invalidate c3) in 
    (cap_is_sealed sealed_cap) = true /\ (cap_is_valid sealed_cap) = true 
    /\ (cap_get_obj_type sealed_cap = SealType.sealed_indirect_entry_ot)
    /\ (cap_is_invalid sealed_sealed_cap) = true /\ (cap_is_invalid sealed_invalid_cap) = true.
    Proof. repeat ( split; try reflexivity ). Qed.
      
  Example seal_indirect_entry_pair_test_1 : 
    let sealed_cap := cap_seal_indirect_entry_pair c5 in 
    let sealed_sealed_cap := cap_seal_indirect_entry_pair sealed_cap in 
    let sealed_invalid_cap := cap_seal_indirect_entry_pair (cap_invalidate c5) in 
    (cap_is_sealed sealed_cap) = true /\ (cap_is_valid sealed_cap) = true 
    /\ (cap_get_obj_type sealed_cap = SealType.sealed_indirect_entry_pair_ot)
    /\ (cap_is_invalid sealed_sealed_cap) = true /\ (cap_is_invalid sealed_invalid_cap) = true.
    Proof. repeat ( split; try reflexivity ). Qed.
        
  Example alloc_cap_test_1 : 
    let value := AddressValue.of_Z 1024 in 
    let new_cap := alloc_cap value (AddressValue.of_Z 2048) in 
    (cap_is_valid new_cap) /\ (cap_get_value new_cap) = value 
    /\ (cap_is_in_bounds new_cap) /\ (cap_is_sealed new_cap) = false 
    /\ (cap_get_seal new_cap) = SealType.Cap_Unsealed 
    /\ (cap_get_perms new_cap) = Permissions.perm_alloc
    /\ (cap_get_bounds_ new_cap) = (Bounds.of_Zs (1024,3072), true).
    Proof. vm_compute. repeat (split; try reflexivity; try bv_solve). Qed. 
  
  Example alloc_cap_test_2 : 
    let value := AddressValue.of_Z 0xffffffffffffffff in (* 16 f's = the largest Value possible *)
    let new_cap := alloc_cap value (AddressValue.of_Z 1) in 
    (cap_is_valid new_cap) = true /\ (cap_get_value new_cap) = value 
    /\ (cap_is_in_bounds new_cap) /\ (cap_is_sealed new_cap) = false 
    /\ (cap_get_seal new_cap) = SealType.Cap_Unsealed 
    /\ (cap_get_perms new_cap) = Permissions.perm_alloc
    /\ (cap_get_bounds_ new_cap) = (Bounds.of_Zs (0xffffffffffffffff,0x10000000000000000), true).
    Proof. vm_compute. repeat (split; try reflexivity; try bv_solve). Qed. 

  Example alloc_cap_test_3 : 
    let value := AddressValue.of_Z 0x10000000000000000 in (* 1 past the largest Value possible; it gets passed as just 0 *)
    let new_cap := alloc_cap value (AddressValue.of_Z 1) in 
    (cap_is_valid new_cap) = true 
    /\ (cap_is_in_bounds new_cap) = true (* it's in bounds bc these are (0,1) *)
    /\ (cap_is_sealed new_cap) = false /\ (cap_get_seal new_cap) = SealType.Cap_Unsealed 
    /\ (cap_get_perms new_cap) = Permissions.perm_alloc  
    /\ (cap_get_bounds_ new_cap) <> (Bounds.of_Zs (0x10000000000000000,0x10000000000000001), true).
    Proof. vm_compute. repeat (split; try reflexivity; try bv_solve). intros H. discriminate H. Qed.

  Example alloc_cap_test_4 : 
    let value := AddressValue.of_Z 0xffffffffffffff in (* 14 f's *)
    let new_cap := alloc_cap value (AddressValue.of_Z 0xfff) in (* this sends the limit above the max limit allowed *)
    (cap_is_invalid new_cap) /\ (cap_is_not_in_bounds new_cap)
    /\ (cap_is_sealed new_cap) = false /\ (cap_get_seal new_cap) = SealType.Cap_Unsealed 
    /\ (cap_get_perms new_cap) = Permissions.perm_alloc  
    /\ (cap_get_bounds_ new_cap) <> (Bounds.of_Zs (0xffffffffffffff,0xfffffffffffffffff), true).
    Proof. vm_compute. repeat (split; try reflexivity). intro H. discriminate H. Qed.   
          
  Example alloc_fun_test_1 : 
    let value := AddressValue.of_Z 1024 in 
    let new_cap := alloc_fun value in 
    (cap_is_valid new_cap) = true /\ (cap_get_value new_cap) = value 
      /\ (cap_is_sealed new_cap) = true /\ (cap_get_seal new_cap) = SealType.Cap_SEntry 
      /\ (cap_get_perms new_cap) = Permissions.perm_alloc_fun
      /\ (cap_get_bounds_ new_cap) = (Bounds.of_Zs (1024,1026), true).
    Proof. repeat (split; try reflexivity; try vm_compute; try bv_solve). Qed. 

  Example cap_is_null_derived_test_1 : 
    let new_cap := cap_c0 () in 
    let new_cap := cap_set_value new_cap (AddressValue.of_Z 512) in 
    (cap_is_null_derived new_cap) = true.
    Proof. vm_compute. reflexivity. Qed.
      
  Example cap_is_null_derived_test_2 : 
    let new_cap := cap_cU () in 
    let new_cap := cap_set_value new_cap (AddressValue.of_Z 512) in 
    (cap_is_null_derived new_cap) = false.
    Proof. vm_compute. reflexivity. Qed.

  Example encode_and_decode_test_1 :     
    let tester := fun cap:Capability.t => 
      let encoded_cap : option ((list ascii) * bool) := encode cap in 
      let decoded_cap : option Capability.t :=
        match encoded_cap with 
          Some (l,tag) => (decode l tag) | None => None
        end in 
      let c_ : Capability.t := 
        match decoded_cap with 
          Some c => c | None => cap_c0 () 
        end in 
        (Capability.eqb c_ cap) = true in
      tester c1 /\ tester c2 /\ tester c3 /\ tester c4 /\ tester c5 /\ tester c6 
      /\ tester c7 /\ tester c8.
    Proof. vm_compute. repeat (split; try reflexivity). Qed.
 
  Example cap_bounds_check_test_1 :
    cap_bounds_check c1 (cap_get_bounds c1) = true.
  Proof. vm_compute. reflexivity. Qed.
  
  Example cap_bounds_check_test_2 :
    cap_bounds_check c4 (cap_get_bounds c3) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example cap_bounds_check_test_3 :
    cap_bounds_check c3 (cap_get_bounds c4) = false.
  Proof. vm_compute. reflexivity. Qed.

End test_cap_getters_and_setters. 
