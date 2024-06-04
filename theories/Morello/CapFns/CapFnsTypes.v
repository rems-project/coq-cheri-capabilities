
Require Import SailStdpp.Base.
Require Import SailStdpp.Real.
Import ListNotations.
Open Scope string.
Open Scope bool.
Open Scope Z.

Definition bits (n : Z) : Type := mword n.

Definition CAP_VALUE_HI_BIT  : Z := 63.
#[export] Hint Unfold CAP_VALUE_HI_BIT : sail.

Definition CAP_VALUE_LO_BIT  : Z := 0.
#[export] Hint Unfold CAP_VALUE_LO_BIT : sail.

Definition CAP_VALUE_NUM_BITS  : Z := (63 - 0 + 1).
#[export] Hint Unfold CAP_VALUE_NUM_BITS : sail.

Definition CAP_BASE_HI_BIT  : Z := 79.
#[export] Hint Unfold CAP_BASE_HI_BIT : sail.

Definition CAP_BASE_LO_BIT  : Z := 64.
#[export] Hint Unfold CAP_BASE_LO_BIT : sail.

Definition CAP_MW  : Z := (79 - 64 + 1).
#[export] Hint Unfold CAP_MW : sail.

Definition CAP_BOUND_NUM_BITS  : Z := (63 - 0 + 1 + 1).
#[export] Hint Unfold CAP_BOUND_NUM_BITS : sail.

Definition CAP_OTYPE_HI_BIT  : Z := 109.
#[export] Hint Unfold CAP_OTYPE_HI_BIT : sail.

Definition CAP_OTYPE_LO_BIT  : Z := 95.
#[export] Hint Unfold CAP_OTYPE_LO_BIT : sail.

Definition CAP_PERMS_HI_BIT  : Z := 127.
#[export] Hint Unfold CAP_PERMS_HI_BIT : sail.

Definition CAP_PERMS_LO_BIT  : Z := 110.
#[export] Hint Unfold CAP_PERMS_LO_BIT : sail.

Definition CAP_PERMS_NUM_BITS  : Z := (127 - 110 + 1).
#[export] Hint Unfold CAP_PERMS_NUM_BITS : sail.

Definition CAP_LENGTH_NUM_BITS  : Z := (63 - 0 + 1 + 1).
#[export] Hint Unfold CAP_LENGTH_NUM_BITS : sail.

Inductive register_value  :=
  | Regval_vector : list register_value -> register_value
  | Regval_list : list register_value -> register_value
  | Regval_option : option register_value -> register_value
  | Regval_bool : bool -> register_value
  | Regval_int : Z -> register_value
  | Regval_real : R -> register_value
  | Regval_string : string -> register_value
  | Regval_bit : bitU -> register_value.
Arguments register_value : clear implicits.

Definition regstate  : Type := unit.



Definition bit_of_regval (merge_var : register_value) : option bitU :=
   match merge_var with | Regval_bit v => Some v | _ => None end.

Definition regval_of_bit (v : bitU) : register_value := Regval_bit v.



Definition bool_of_regval (merge_var : register_value) : option bool :=
  match merge_var with | Regval_bool v => Some v | _ => None end.

Definition regval_of_bool (v : bool) : register_value := Regval_bool v.

Definition int_of_regval (merge_var : register_value) : option Z :=
  match merge_var with | Regval_int v => Some v | _ => None end.

Definition regval_of_int (v : Z) : register_value := Regval_int v.

Definition real_of_regval (merge_var : register_value) : option R :=
  match merge_var with | Regval_real v => Some v | _ => None end.

Definition regval_of_real (v : R) : register_value := Regval_real v.

Definition string_of_regval (merge_var : register_value) : option string :=
  match merge_var with | Regval_string v => Some v | _ => None end.

Definition regval_of_string (v : string) : register_value := Regval_string v.

Definition vector_of_regval {a} n (of_regval : register_value -> option a) (rv : register_value) : option (vec a n) := match rv with
  | Regval_vector v => if n =? length_list v then map_bind (vec_of_list n) (just_list (List.map of_regval v)) else None
  | _ => None
end.

Definition regval_of_vector {a size} (regval_of : a -> register_value) (xs : vec a size) : register_value := Regval_vector (List.map regval_of (list_of_vec xs)).

Definition list_of_regval {a} (of_regval : register_value -> option a) (rv : register_value) : option (list a) := match rv with
  | Regval_list v => just_list (List.map of_regval v)
  | _ => None
end.

Definition regval_of_list {a} (regval_of : a -> register_value) (xs : list a) : register_value := Regval_list (List.map regval_of xs).

Definition option_of_regval {a} (of_regval : register_value -> option a) (rv : register_value) : option (option a) := match rv with
  | Regval_option v => option_map of_regval v
  | _ => None
end.

Definition regval_of_option {a} (regval_of : a -> register_value) (v : option a) := Regval_option (option_map regval_of v).



Local Open Scope string.
Definition get_regval (reg_name : string) (s : regstate) : option register_value :=

  None.

Definition set_regval (reg_name : string) (v : register_value) (s : regstate) : option regstate :=

  None.

Definition register_accessors := (get_regval, set_regval).


Definition MR a r := monadR register_value a r unit.
Definition M a := monad register_value a unit.
Definition returnM {A:Type} := @returnm register_value A unit.
Definition returnR {A:Type} (R:Type) := @returnm register_value A (R + unit).