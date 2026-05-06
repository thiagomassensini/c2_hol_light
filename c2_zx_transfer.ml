(* ------------------------------------------------------------------------- *)
(* C2 route K: exact ZX transfer identity.                                   *)
(*                                                                           *)
(* Lean reference:                                                           *)
(*   formal/lean_c2/LeanC2/Transfer.lean                                      *)
(*                                                                           *)
(* This HOL layer ports the algebraic transfer map                            *)
(*   Z_X = zeta + R / c0                                                      *)
(* and proves the exact norm identity and its lower-bound consequences.       *)
(* ------------------------------------------------------------------------- *)

prioritize_complex();;

let c2_zx = new_definition
 `c2_zx zeta R c0 = zeta + R / c0`;;

let C2_ZX_TRANSFER_EXACT = prove
 (`!zeta R c0. norm(c2_zx zeta R c0 - zeta) = norm(R / c0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c2_zx] THEN
  AP_TERM_TAC THEN
  SIMPLE_COMPLEX_ARITH_TAC);;

let C2_ZX_TRANSFER_BOUND = prove
 (`!zeta R c0 B.
      norm(R / c0) <= B
      ==> norm(c2_zx zeta R c0 - zeta) <= B`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[C2_ZX_TRANSFER_EXACT]);;

let C2_ZX_TRANSFER_DIV_NORM = prove
 (`!zeta R c0.
      norm(c2_zx zeta R c0 - zeta) = norm(R) / norm(c0)`,
  REWRITE_TAC[C2_ZX_TRANSFER_EXACT; COMPLEX_NORM_DIV]);;

let C2_ZX_TRANSFER_GENUINE_ERROR = prove
 (`!zeta R c0.
      norm(c2_zx zeta R c0 - zeta) =
      c2_genuine_transfer_error (norm(R)) (norm(c0))`,
  REWRITE_TAC[C2_ZX_TRANSFER_DIV_NORM; c2_genuine_transfer_error]);;

let C2_ZX_TRANSFER_BOUND_FROM_LOWER = prove
 (`!zeta R c0 L B.
      &0 < L /\ L <= norm(c0) /\ norm(R) <= B * L
      ==> norm(c2_zx zeta R c0 - zeta) <= B`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[C2_ZX_TRANSFER_GENUINE_ERROR] THEN
  MATCH_MP_TAC C2_GENUINE_TRANSFER_BOUND THEN
  EXISTS_TAC `L:real` THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_POS]);;

let C2_ZX_TRANSFER_FINITE_BOUND = prove
 (`!zeta c0 X C theta L B.
      &0 < X /\ norm(theta) <= &1 /\
      &0 < L /\ L <= norm(c0) /\ abs(C) <= B * L * X
      ==> norm(c2_zx zeta (c2_finite_residual X C theta) c0 - zeta) <= B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C2_ZX_TRANSFER_BOUND_FROM_LOWER THEN
  EXISTS_TAC `L:real` THEN
  ASM_REWRITE_TAC[GSYM c2_finite_residual_norm] THEN
  MATCH_MP_TAC C2_FINITE_RESIDUAL_BOUND_FROM_COEFFICIENT THEN
  ASM_REWRITE_TAC[]);;

let C2_ZX_TRANSFER_FINITE_CANONICAL_BOUND = prove
 (`!zeta c0 X C L B.
      &0 < X /\ &0 < L /\ L <= norm(c0) /\
      abs(C) <= B * L * X
      ==> norm(c2_zx zeta (c2_finite_residual_canonical X C) c0 - zeta) <= B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C2_ZX_TRANSFER_BOUND_FROM_LOWER THEN
  EXISTS_TAC `L:real` THEN
  ASM_REWRITE_TAC[GSYM c2_finite_residual_canonical_norm] THEN
  MATCH_MP_TAC C2_FINITE_RESIDUAL_CANONICAL_BOUND_FROM_COEFFICIENT THEN
  ASM_REWRITE_TAC[]);;

let C2_BRIDGE_FINITE_ZX_CRITICAL = prove
 (`!t zeta c0 X C theta L B.
      &0 < X /\ norm(theta) <= &1 /\
      &0 < L /\ L <= norm(c0) /\ abs(C) <= B * L * X
      ==> c2_branch_norm_sq_sigma_t (&1 / &2) t = &1 /\
          norm(c2_zx zeta (c2_finite_residual X C theta) c0 - zeta) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[c2_branch_norm_sq_sigma_t; C2_BRANCH_NORM_SQ_HALF];
    MATCH_MP_TAC C2_ZX_TRANSFER_FINITE_BOUND THEN
    EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[]]);;

let C2_BRIDGE_FINITE_ZX_OFFAXIS = prove
 (`!sigma t zeta c0 X C theta L B.
      &0 < sigma /\ &1 / &2 < sigma /\
      &0 < X /\ norm(theta) <= &1 /\
      &0 < L /\ L <= norm(c0) /\ abs(C) <= B * L * X
      ==> c2_branch_norm_sq_sigma_t sigma t < &1 /\
          norm(c2_zx zeta (c2_finite_residual X C theta) c0 - zeta) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[c2_branch_norm_sq_sigma_t] THEN
    ASM_MESON_TAC[C2_BRANCH_NORM_SQ_LT_ONE_IFF];
    MATCH_MP_TAC C2_ZX_TRANSFER_FINITE_BOUND THEN
    EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[]]);;

let C2_BRIDGE_FINITE_ZX_OFFAXIS_EXPANSIVE_SIDE = prove
 (`!sigma t zeta c0 X C theta L B.
      &0 < sigma /\ sigma < &1 / &2 /\
      &0 < X /\ norm(theta) <= &1 /\
      &0 < L /\ L <= norm(c0) /\ abs(C) <= B * L * X
      ==> &1 < c2_branch_norm_sq_sigma_t sigma t /\
          norm(c2_zx zeta (c2_finite_residual X C theta) c0 - zeta) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[c2_branch_norm_sq_sigma_t] THEN
    ASM_MESON_TAC[C2_BRANCH_NORM_SQ_GT_ONE_IFF];
    MATCH_MP_TAC C2_ZX_TRANSFER_FINITE_BOUND THEN
    EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[]]);;

let C2_BRIDGE_FINITE_CANONICAL_ZX_OFFAXIS = prove
 (`!sigma t zeta c0 X C L B.
      &0 < sigma /\ &1 / &2 < sigma /\
      &0 < X /\ &0 < L /\ L <= norm(c0) /\
      abs(C) <= B * L * X
      ==> c2_branch_norm_sq_sigma_t sigma t < &1 /\
          norm(c2_zx zeta (c2_finite_residual_canonical X C) c0 - zeta) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[c2_branch_norm_sq_sigma_t] THEN
    ASM_MESON_TAC[C2_BRANCH_NORM_SQ_LT_ONE_IFF];
    MATCH_MP_TAC C2_ZX_TRANSFER_FINITE_CANONICAL_BOUND THEN
    EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[]]);;

