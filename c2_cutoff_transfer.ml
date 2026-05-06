(* ------------------------------------------------------------------------- *)
(* C2 route K: cutoff residual transfer into the genuine bridge.             *)
(*                                                                           *)
(* Lean reference:                                                           *)
(*   formal/lean_c2/LeanC2/Transfer.lean                                      *)
(*                                                                           *)
(* This HOL layer ports the finite cutoff residual R_X = C / X and proves     *)
(* that a coefficient bound |C| <= B * L * X supplies the residual hypothesis *)
(* required by the norm-level genuine bridge.                                *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let C2_REAL_ABS_OF_POS = prove
 (`!x. &0 < x ==> abs(x) = x`,
  REAL_ARITH_TAC);;

let c2_cutoff_residual = new_definition
 `c2_cutoff_residual X C = C / X`;;

let c2_cutoff_residual_norm = new_definition
 `c2_cutoff_residual_norm X C = abs(c2_cutoff_residual X C)`;;

let C2_CUTOFF_RESIDUAL_NORM_NONNEG = prove
 (`!X C. &0 <= c2_cutoff_residual_norm X C`,
  REWRITE_TAC[c2_cutoff_residual_norm; REAL_ABS_POS]);;

let C2_CUTOFF_RESIDUAL_ABS = prove
 (`!X C. &0 < X
         ==> c2_cutoff_residual_norm X C = abs(C) / X`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[c2_cutoff_residual_norm; c2_cutoff_residual; REAL_ABS_DIV] THEN
  ASM_SIMP_TAC[C2_REAL_ABS_OF_POS]);;

let C2_CUTOFF_RESIDUAL_BIG_O = prove
 (`!X C K. &0 < X /\ abs(C) <= K
           ==> c2_cutoff_residual_norm X C <= K / X`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[C2_CUTOFF_RESIDUAL_ABS; REAL_LE_DIV2_EQ]);;

let C2_CUTOFF_RESIDUAL_BOUND_FROM_COEFFICIENT = prove
 (`!X C L B. &0 < X /\ abs(C) <= B * L * X
             ==> c2_cutoff_residual_norm X C <= B * L`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[C2_CUTOFF_RESIDUAL_ABS; REAL_LE_LDIV_EQ] THEN
  ASM_REAL_ARITH_TAC);;

let C2_CUTOFF_TO_GENUINE_TRANSFER_BOUND = prove
 (`!X C c0_norm L B.
      &0 < X /\ &0 < L /\ L <= c0_norm /\
      abs(C) <= B * L * X
      ==> c2_genuine_transfer_error
            (c2_cutoff_residual_norm X C) c0_norm <= B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C2_GENUINE_TRANSFER_BOUND THEN
  EXISTS_TAC `L:real` THEN
  ASM_REWRITE_TAC[C2_CUTOFF_RESIDUAL_NORM_NONNEG] THEN
  MATCH_MP_TAC C2_CUTOFF_RESIDUAL_BOUND_FROM_COEFFICIENT THEN
  ASM_REWRITE_TAC[]);;

let C2_BRIDGE_CUTOFF_TO_GENUINE_CRITICAL = prove
 (`!t X C c0_norm L B.
      &0 < X /\ &0 < L /\ L <= c0_norm /\
      abs(C) <= B * L * X
      ==> c2_branch_norm_sq_sigma_t (&1 / &2) t = &1 /\
          c2_genuine_transfer_error
            (c2_cutoff_residual_norm X C) c0_norm <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C2_BRIDGE_BRANCH_TO_GENUINE_CRITICAL THEN
  EXISTS_TAC `L:real` THEN
  ASM_REWRITE_TAC[C2_CUTOFF_RESIDUAL_NORM_NONNEG] THEN
  MATCH_MP_TAC C2_CUTOFF_RESIDUAL_BOUND_FROM_COEFFICIENT THEN
  ASM_REWRITE_TAC[]);;

let C2_BRIDGE_CUTOFF_TO_GENUINE_OFFAXIS = prove
 (`!sigma t X C c0_norm L B.
      &0 < sigma /\ &1 / &2 < sigma /\
      &0 < X /\ &0 < L /\ L <= c0_norm /\
      abs(C) <= B * L * X
      ==> c2_branch_norm_sq_sigma_t sigma t < &1 /\
          c2_genuine_transfer_error
            (c2_cutoff_residual_norm X C) c0_norm <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C2_BRIDGE_BRANCH_TO_GENUINE_OFFAXIS THEN
  EXISTS_TAC `L:real` THEN
  ASM_REWRITE_TAC[C2_CUTOFF_RESIDUAL_NORM_NONNEG] THEN
  MATCH_MP_TAC C2_CUTOFF_RESIDUAL_BOUND_FROM_COEFFICIENT THEN
  ASM_REWRITE_TAC[]);;

let C2_BRIDGE_CUTOFF_TO_GENUINE_OFFAXIS_EXPANSIVE_SIDE = prove
 (`!sigma t X C c0_norm L B.
      &0 < sigma /\ sigma < &1 / &2 /\
      &0 < X /\ &0 < L /\ L <= c0_norm /\
      abs(C) <= B * L * X
      ==> &1 < c2_branch_norm_sq_sigma_t sigma t /\
          c2_genuine_transfer_error
            (c2_cutoff_residual_norm X C) c0_norm <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C2_BRIDGE_BRANCH_TO_GENUINE_OFFAXIS_EXPANSIVE_SIDE THEN
  EXISTS_TAC `L:real` THEN
  ASM_REWRITE_TAC[C2_CUTOFF_RESIDUAL_NORM_NONNEG] THEN
  MATCH_MP_TAC C2_CUTOFF_RESIDUAL_BOUND_FROM_COEFFICIENT THEN
  ASM_REWRITE_TAC[]);;
