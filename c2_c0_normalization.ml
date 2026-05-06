(* ------------------------------------------------------------------------- *)
(* C2 route K: c0 normalization profile, HOL Light port.                    *)
(*                                                                           *)
(* Lean references:                                                          *)
(*   formal/lean_c2/LeanC2/Normalization.lean                                *)
(*   formal/lean_c2/LeanC2/Transfer.lean, c0OffAxisLower section             *)
(*                                                                           *)
(* This layer ports the real sigma profile used by the c0 lower-bound        *)
(* transfer chain.  It does not use numerical testing: every statement below *)
(* is a HOL theorem checked by the kernel.                                    *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let c2_two_pow_real = new_definition
 `c2_two_pow_real sigma = exp(sigma * ln(&2))`;;

let c2_c0_real = new_definition
 `c2_c0_real sigma =
    exp(--(&2 * sigma * ln(&2))) * (c2_two_pow_real sigma - &1) /
    (&2 * c2_two_pow_real sigma - &1)`;;

let c2_c0_offaxis_lower = new_definition
 `c2_c0_offaxis_lower sigma =
    exp(--(&2 * sigma * ln(&2))) * (c2_two_pow_real sigma - &1) /
    (&2 * c2_two_pow_real sigma + &1)`;;

let c2_c0_critical_lower = new_definition
 `c2_c0_critical_lower = c2_c0_offaxis_lower (&1 / &2)`;;

let C2_TWO_POW_REAL_POS_LT = prove
 (`!sigma. &0 < c2_two_pow_real sigma`,
  REWRITE_TAC[c2_two_pow_real; REAL_EXP_POS_LT]);;

let C2_TWO_POW_REAL_GT_ONE = prove
 (`!sigma. &0 < sigma ==> &1 < c2_two_pow_real sigma`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[c2_two_pow_real; GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN
  ASM_REWRITE_TAC[C2_LN2_POS]);;

let C2_C0_REAL_POS = prove
 (`!sigma. &0 < sigma ==> &0 < c2_c0_real sigma`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[c2_c0_real; real_div] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT];
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MP_TAC(SPEC `sigma:real` C2_TWO_POW_REAL_GT_ONE) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN
      MP_TAC(SPEC `sigma:real` C2_TWO_POW_REAL_GT_ONE) THEN
      ASM_REAL_ARITH_TAC]]);;

let C2_C0_REAL_NE_ZERO = prove
 (`!sigma. &0 < sigma ==> ~(c2_c0_real sigma = &0)`,
  MESON_TAC[C2_C0_REAL_POS; REAL_LT_IMP_NZ]);;

let C2_C0_OFFAXIS_LOWER_POS = prove
 (`!sigma. &0 < sigma ==> &0 < c2_c0_offaxis_lower sigma`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[c2_c0_offaxis_lower; real_div] THEN
  MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_EXP_POS_LT];
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [MP_TAC(SPEC `sigma:real` C2_TWO_POW_REAL_GT_ONE) THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_INV THEN
      MP_TAC(SPEC `sigma:real` C2_TWO_POW_REAL_POS_LT) THEN
      REAL_ARITH_TAC]]);;

let C2_C0_OFFAXIS_LOWER_NONNEG = prove
 (`!sigma. &0 < sigma ==> &0 <= c2_c0_offaxis_lower sigma`,
  MESON_TAC[C2_C0_OFFAXIS_LOWER_POS; REAL_LT_IMP_LE]);;

let C2_C0_OFFAXIS_LOWER_NE_ZERO = prove
 (`!sigma. &0 < sigma ==> ~(c2_c0_offaxis_lower sigma = &0)`,
  MESON_TAC[C2_C0_OFFAXIS_LOWER_POS; REAL_LT_IMP_NZ]);;

let C2_C0_OFFAXIS_LOWER_LE_REAL = prove
 (`!sigma. &0 < sigma ==> c2_c0_offaxis_lower sigma <= c2_c0_real sigma`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[c2_c0_offaxis_lower; c2_c0_real] THEN
  ABBREV_TAC `p = c2_two_pow_real sigma` THEN
  SUBGOAL_THEN `&1 < p` ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN
    MATCH_MP_TAC C2_TWO_POW_REAL_GT_ONE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_LE THEN
    REWRITE_TAC[REAL_EXP_POS_LT];
    MATCH_MP_TAC REAL_LE_LMUL THEN
    CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_REAL_ARITH_TAC]]);;

let C2_C0_CRITICAL_LOWER_POS = prove
 (`&0 < c2_c0_critical_lower`,
  REWRITE_TAC[c2_c0_critical_lower] THEN
  MATCH_MP_TAC C2_C0_OFFAXIS_LOWER_POS THEN
  REAL_ARITH_TAC);;

let C2_C0_CRITICAL_LOWER_NE_ZERO = prove
 (`~(c2_c0_critical_lower = &0)`,
  MESON_TAC[C2_C0_CRITICAL_LOWER_POS; REAL_LT_IMP_NZ]);;

let C2_C0_CRITICAL_LOWER_LE_REAL_HALF = prove
 (`c2_c0_critical_lower <= c2_c0_real (&1 / &2)`,
  REWRITE_TAC[c2_c0_critical_lower] THEN
  MATCH_MP_TAC C2_C0_OFFAXIS_LOWER_LE_REAL THEN
  REAL_ARITH_TAC);;

prioritize_complex();;

let c2_c0_offaxis_profile_realized = new_definition
 `c2_c0_offaxis_profile_realized (c0st:real->real->complex) <=>
    !sigma t. &0 < sigma
              ==> c2_c0_offaxis_lower sigma <= norm(c0st sigma t)`;;

let c2_c0_critical_profile_realized = new_definition
 `c2_c0_critical_profile_realized (c0crit:real->complex) <=>
    !t. c2_c0_critical_lower <= norm(c0crit t)`;;

let C2_C0_OFFAXIS_PROFILE_POINT = prove
 (`!(c0st:real->real->complex) sigma t.
      c2_c0_offaxis_profile_realized c0st /\ &0 < sigma
      ==> c2_c0_offaxis_lower sigma <= norm(c0st sigma t)`,
  REWRITE_TAC[c2_c0_offaxis_profile_realized] THEN MESON_TAC[]);;

let C2_C0_CRITICAL_PROFILE_POINT = prove
 (`!(c0crit:real->complex) t.
      c2_c0_critical_profile_realized c0crit
      ==> c2_c0_critical_lower <= norm(c0crit t)`,
  REWRITE_TAC[c2_c0_critical_profile_realized] THEN MESON_TAC[]);;

let C2_C0_OFFAXIS_PROFILE_TRANSFER_CANONICAL = prove
 (`!(c0st:real->real->complex) zeta X C B sigma t.
      c2_c0_offaxis_profile_realized c0st /\
      &0 < sigma /\ &0 < X /\
      abs(C) <= B * c2_c0_offaxis_lower sigma * X
      ==> norm(c2_zx zeta (c2_finite_residual_canonical X C)
               (c0st sigma t) - zeta) <= B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C2_ZX_TRANSFER_FINITE_CANONICAL_BOUND THEN
  EXISTS_TAC `c2_c0_offaxis_lower sigma` THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC C2_C0_OFFAXIS_LOWER_POS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C2_C0_OFFAXIS_PROFILE_POINT THEN
    ASM_REWRITE_TAC[]]);;

let C2_C0_OFFAXIS_PROFILE_TRANSFER = prove
 (`!(c0st:real->real->complex) zeta X C theta B sigma t.
      c2_c0_offaxis_profile_realized c0st /\
      &0 < sigma /\ &0 < X /\ norm(theta) <= &1 /\
      abs(C) <= B * c2_c0_offaxis_lower sigma * X
      ==> norm(c2_zx zeta (c2_finite_residual X C theta)
               (c0st sigma t) - zeta) <= B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C2_ZX_TRANSFER_FINITE_BOUND THEN
  EXISTS_TAC `c2_c0_offaxis_lower sigma` THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC C2_C0_OFFAXIS_LOWER_POS THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC C2_C0_OFFAXIS_PROFILE_POINT THEN
    ASM_REWRITE_TAC[]]);;

let C2_C0_CRITICAL_PROFILE_TRANSFER_CANONICAL = prove
 (`!(c0crit:real->complex) zeta X C B t.
      c2_c0_critical_profile_realized c0crit /\
      &0 < X /\
      abs(C) <= B * c2_c0_critical_lower * X
      ==> norm(c2_zx zeta (c2_finite_residual_canonical X C)
               (c0crit t) - zeta) <= B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C2_ZX_TRANSFER_FINITE_CANONICAL_BOUND THEN
  EXISTS_TAC `c2_c0_critical_lower` THEN
  ASM_REWRITE_TAC[C2_C0_CRITICAL_LOWER_POS] THEN
  MATCH_MP_TAC C2_C0_CRITICAL_PROFILE_POINT THEN
  ASM_REWRITE_TAC[]);;

let C2_C0_CRITICAL_PROFILE_TRANSFER = prove
 (`!(c0crit:real->complex) zeta X C theta B t.
      c2_c0_critical_profile_realized c0crit /\
      &0 < X /\ norm(theta) <= &1 /\
      abs(C) <= B * c2_c0_critical_lower * X
      ==> norm(c2_zx zeta (c2_finite_residual X C theta)
               (c0crit t) - zeta) <= B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C2_ZX_TRANSFER_FINITE_BOUND THEN
  EXISTS_TAC `c2_c0_critical_lower` THEN
  ASM_REWRITE_TAC[C2_C0_CRITICAL_LOWER_POS] THEN
  MATCH_MP_TAC C2_C0_CRITICAL_PROFILE_POINT THEN
  ASM_REWRITE_TAC[]);;
