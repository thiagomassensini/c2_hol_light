(* ------------------------------------------------------------------------- *)
(* C2 route K: concrete finite residual witness.                             *)
(*                                                                           *)
(* Lean reference:                                                           *)
(*   formal/lean_c2/LeanC2/Transfer.lean                                      *)
(*                                                                           *)
(* This HOL layer ports the complex finite residual                           *)
(*   R_X(theta) = Cx(C / X) * theta                                           *)
(* and proves that a unit-bounded shape factor is controlled by the cutoff    *)
(* model already formalized in c2_cutoff_transfer.ml.                        *)
(* ------------------------------------------------------------------------- *)

prioritize_complex();;

let c2_finite_residual = new_definition
 `c2_finite_residual X C (theta:complex) =
    Cx(c2_cutoff_residual X C) * theta`;;

let c2_finite_residual_norm = new_definition
 `c2_finite_residual_norm X C (theta:complex) =
    norm(c2_finite_residual X C theta)`;;

let c2_finite_residual_canonical = new_definition
 `c2_finite_residual_canonical X C =
    c2_finite_residual X C (Cx(&1))`;;

let c2_finite_residual_canonical_norm = new_definition
 `c2_finite_residual_canonical_norm X C =
    norm(c2_finite_residual_canonical X C)`;;

let C2_FINITE_RESIDUAL_NORM_NONNEG = prove
 (`!X C theta. &0 <= c2_finite_residual_norm X C theta`,
  REWRITE_TAC[c2_finite_residual_norm; COMPLEX_NORM_POS]);;

let C2_FINITE_RESIDUAL_NORM = prove
 (`!X C theta.
      c2_finite_residual_norm X C theta =
      c2_cutoff_residual_norm X C * norm(theta)`,
  REWRITE_TAC[c2_finite_residual_norm; c2_finite_residual;
              c2_cutoff_residual_norm; COMPLEX_NORM_MUL;
              COMPLEX_NORM_CX]);;

let C2_FINITE_RESIDUAL_NORM_LE_CUTOFF_OF_UNIT = prove
 (`!X C theta.
      norm(theta) <= &1
      ==> c2_finite_residual_norm X C theta <=
          c2_cutoff_residual_norm X C`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[C2_FINITE_RESIDUAL_NORM] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c2_cutoff_residual_norm X C * &1` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_REWRITE_TAC[C2_CUTOFF_RESIDUAL_NORM_NONNEG];
    REAL_ARITH_TAC]);;

let C2_FINITE_RESIDUAL_BOUND_FROM_COEFFICIENT = prove
 (`!X C theta L B.
      &0 < X /\ norm(theta) <= &1 /\ abs(C) <= B * L * X
      ==> c2_finite_residual_norm X C theta <= B * L`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c2_cutoff_residual_norm X C` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC C2_FINITE_RESIDUAL_NORM_LE_CUTOFF_OF_UNIT THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC C2_CUTOFF_RESIDUAL_BOUND_FROM_COEFFICIENT THEN
    ASM_REWRITE_TAC[]]);;

let C2_FINITE_RESIDUAL_TO_GENUINE_TRANSFER_BOUND = prove
 (`!X C theta c0_norm L B.
      &0 < X /\ norm(theta) <= &1 /\
      &0 < L /\ L <= c0_norm /\ abs(C) <= B * L * X
      ==> c2_genuine_transfer_error
            (c2_finite_residual_norm X C theta) c0_norm <= B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C2_GENUINE_TRANSFER_BOUND THEN
  EXISTS_TAC `L:real` THEN
  ASM_REWRITE_TAC[C2_FINITE_RESIDUAL_NORM_NONNEG] THEN
  MATCH_MP_TAC C2_FINITE_RESIDUAL_BOUND_FROM_COEFFICIENT THEN
  ASM_REWRITE_TAC[]);;

let C2_BRIDGE_FINITE_TO_GENUINE_CRITICAL = prove
 (`!t X C theta c0_norm L B.
      &0 < X /\ norm(theta) <= &1 /\
      &0 < L /\ L <= c0_norm /\ abs(C) <= B * L * X
      ==> c2_branch_norm_sq_sigma_t (&1 / &2) t = &1 /\
          c2_genuine_transfer_error
            (c2_finite_residual_norm X C theta) c0_norm <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C2_BRIDGE_BRANCH_TO_GENUINE_CRITICAL THEN
  EXISTS_TAC `L:real` THEN
  ASM_REWRITE_TAC[C2_FINITE_RESIDUAL_NORM_NONNEG] THEN
  MATCH_MP_TAC C2_FINITE_RESIDUAL_BOUND_FROM_COEFFICIENT THEN
  ASM_REWRITE_TAC[]);;

let C2_BRIDGE_FINITE_TO_GENUINE_OFFAXIS = prove
 (`!sigma t X C theta c0_norm L B.
      &0 < sigma /\ &1 / &2 < sigma /\
      &0 < X /\ norm(theta) <= &1 /\
      &0 < L /\ L <= c0_norm /\ abs(C) <= B * L * X
      ==> c2_branch_norm_sq_sigma_t sigma t < &1 /\
          c2_genuine_transfer_error
            (c2_finite_residual_norm X C theta) c0_norm <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C2_BRIDGE_BRANCH_TO_GENUINE_OFFAXIS THEN
  EXISTS_TAC `L:real` THEN
  ASM_REWRITE_TAC[C2_FINITE_RESIDUAL_NORM_NONNEG] THEN
  MATCH_MP_TAC C2_FINITE_RESIDUAL_BOUND_FROM_COEFFICIENT THEN
  ASM_REWRITE_TAC[]);;

let C2_BRIDGE_FINITE_TO_GENUINE_OFFAXIS_EXPANSIVE_SIDE = prove
 (`!sigma t X C theta c0_norm L B.
      &0 < sigma /\ sigma < &1 / &2 /\
      &0 < X /\ norm(theta) <= &1 /\
      &0 < L /\ L <= c0_norm /\ abs(C) <= B * L * X
      ==> &1 < c2_branch_norm_sq_sigma_t sigma t /\
          c2_genuine_transfer_error
            (c2_finite_residual_norm X C theta) c0_norm <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C2_BRIDGE_BRANCH_TO_GENUINE_OFFAXIS_EXPANSIVE_SIDE THEN
  EXISTS_TAC `L:real` THEN
  ASM_REWRITE_TAC[C2_FINITE_RESIDUAL_NORM_NONNEG] THEN
  MATCH_MP_TAC C2_FINITE_RESIDUAL_BOUND_FROM_COEFFICIENT THEN
  ASM_REWRITE_TAC[]);;

let C2_FINITE_RESIDUAL_CANONICAL_NORM_LE_CUTOFF = prove
  (`!X C.
      c2_finite_residual_canonical_norm X C <=
      c2_cutoff_residual_norm X C`,
  REWRITE_TAC[c2_finite_residual_canonical_norm;
              c2_finite_residual_canonical;
              c2_finite_residual; c2_cutoff_residual_norm;
              COMPLEX_NORM_MUL; COMPLEX_NORM_CX; COMPLEX_NORM_NUM] THEN
  REAL_ARITH_TAC);;

let C2_FINITE_RESIDUAL_CANONICAL_BOUND_FROM_COEFFICIENT = prove
 (`!X C L B.
      &0 < X /\ abs(C) <= B * L * X
      ==> c2_finite_residual_canonical_norm X C <= B * L`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `c2_cutoff_residual_norm X C` THEN
  ASM_REWRITE_TAC[C2_FINITE_RESIDUAL_CANONICAL_NORM_LE_CUTOFF] THEN
  MATCH_MP_TAC C2_CUTOFF_RESIDUAL_BOUND_FROM_COEFFICIENT THEN
  ASM_REWRITE_TAC[]);;

let C2_BRIDGE_FINITE_CANONICAL_TO_GENUINE_OFFAXIS = prove
 (`!sigma t X C c0_norm L B.
      &0 < sigma /\ &1 / &2 < sigma /\
      &0 < X /\ &0 < L /\ L <= c0_norm /\
      abs(C) <= B * L * X
      ==> c2_branch_norm_sq_sigma_t sigma t < &1 /\
          c2_genuine_transfer_error
            (c2_finite_residual_canonical_norm X C) c0_norm <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C2_BRIDGE_BRANCH_TO_GENUINE_OFFAXIS THEN
  EXISTS_TAC `L:real` THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[c2_finite_residual_canonical_norm; COMPLEX_NORM_POS];
    MATCH_MP_TAC C2_FINITE_RESIDUAL_CANONICAL_BOUND_FROM_COEFFICIENT THEN
    ASM_REWRITE_TAC[]]);;
