(* ------------------------------------------------------------------------- *)
(* C2 route K: genuine complex c0 profile, HOL Light port.                  *)
(*                                                                           *)
(* Lean references:                                                          *)
(*   formal/lean_c2/LeanC2/Normalization.lean                                *)
(*   formal/lean_c2/LeanC2/Transfer.lean, c0Complex_norm_ge_c0OffAxisLower   *)
(*                                                                           *)
(* This layer realizes the explicit off-axis lower profile for the genuine   *)
(* complex normalization coefficient in polar form.  All statements are HOL  *)
(* theorems checked by the kernel.                                            *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let C2_C0_OFFAXIS_LOWER_SCALE_BOUND = prove
 (`!sigma d.
      &0 < sigma /\ d <= &2 * c2_two_pow_real sigma + &1
      ==> c2_c0_offaxis_lower sigma * d <=
          exp(--(&2 * sigma * ln(&2))) * (c2_two_pow_real sigma - &1)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `c2_c0_offaxis_lower sigma * (&2 * c2_two_pow_real sigma + &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[C2_C0_OFFAXIS_LOWER_NONNEG];
    REWRITE_TAC[c2_c0_offaxis_lower; real_div] THEN
    ABBREV_TAC `p = c2_two_pow_real sigma` THEN
    SUBGOAL_THEN `&0 < &2 * p + &1` ASSUME_TAC THENL
     [EXPAND_TAC "p" THEN
      MP_TAC(SPEC `sigma:real` C2_TWO_POW_REAL_POS_LT) THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `&0 < &2 * p + &1` THEN
      CONV_TAC REAL_FIELD]]);;

prioritize_complex();;

let c2_unit_phase = new_definition
 `c2_unit_phase theta = complex(cos theta,sin theta)`;;

let c2_two_pow_complex = new_definition
 `c2_two_pow_complex sigma t =
    Cx(c2_two_pow_real sigma) * c2_unit_phase(t * ln(&2))`;;

let c2_two_pow_neg2_complex = new_definition
 `c2_two_pow_neg2_complex sigma t =
    Cx(exp(--(&2 * sigma * ln(&2)))) *
    c2_unit_phase(--(&2 * t * ln(&2)))`;;

let c2_c0_complex = new_definition
 `c2_c0_complex sigma t =
    c2_two_pow_neg2_complex sigma t *
    (c2_two_pow_complex sigma t - Cx(&1)) /
    (Cx(&2) * c2_two_pow_complex sigma t - Cx(&1))`;;

let C2_UNIT_PHASE_NORM = prove
 (`!theta. norm(c2_unit_phase theta) = &1`,
  REWRITE_TAC[c2_unit_phase; complex_norm; RE; IM] THEN
  ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
  REWRITE_TAC[SIN_CIRCLE; SQRT_1]);;

let C2_TWO_POW_COMPLEX_NORM = prove
 (`!sigma t. norm(c2_two_pow_complex sigma t) = c2_two_pow_real sigma`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c2_two_pow_complex; COMPLEX_NORM_MUL; COMPLEX_NORM_CX;
              C2_UNIT_PHASE_NORM; REAL_MUL_RID] THEN
  SIMP_TAC[REAL_ABS_REFL; REAL_LT_IMP_LE; C2_TWO_POW_REAL_POS_LT]);;

let C2_TWO_POW_NEG2_COMPLEX_NORM = prove
 (`!sigma t.
      norm(c2_two_pow_neg2_complex sigma t) =
      exp(--(&2 * sigma * ln(&2)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c2_two_pow_neg2_complex; COMPLEX_NORM_MUL; COMPLEX_NORM_CX;
              C2_UNIT_PHASE_NORM; REAL_MUL_RID] THEN
  SIMP_TAC[REAL_ABS_REFL; REAL_EXP_POS_LE]);;

let C2_C0_COMPLEX_DENOM_NZ = prove
 (`!sigma t.
      &0 < sigma
      ==> ~(Cx(&2) * c2_two_pow_complex sigma t - Cx(&1) = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC
   `Cx(&2) * c2_two_pow_complex sigma t - Cx(&1) = Cx(&0)` THEN
  REWRITE_TAC[COMPLEX_SUB_0] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o AP_TERM `norm`) THEN
  REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_CX; REAL_ABS_NUM;
              C2_TWO_POW_COMPLEX_NORM] THEN
  MP_TAC(SPEC `sigma:real` C2_TWO_POW_REAL_GT_ONE) THEN
  ASM_REAL_ARITH_TAC);;

let C2_C0_COMPLEX_DENOM_NORM_POS = prove
 (`!sigma t.
      &0 < sigma
      ==> &0 < norm(Cx(&2) * c2_two_pow_complex sigma t - Cx(&1))`,
  SIMP_TAC[COMPLEX_NORM_NZ; C2_C0_COMPLEX_DENOM_NZ]);;

let C2_C0_COMPLEX_NUMERATOR_NORM_LOWER = prove
 (`!sigma t.
      &0 < sigma
      ==> exp(--(&2 * sigma * ln(&2))) *
          (c2_two_pow_real sigma - &1)
          <= norm(c2_two_pow_neg2_complex sigma t *
                  (c2_two_pow_complex sigma t - Cx(&1)))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `u = c2_two_pow_complex sigma t` THEN
  ABBREV_TAC `a = c2_two_pow_neg2_complex sigma t` THEN
  SUBGOAL_THEN `norm(u:complex) = c2_two_pow_real sigma` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REWRITE_TAC[C2_TWO_POW_COMPLEX_NORM];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(a:complex) = exp(--(&2 * sigma * ln(&2)))` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN REWRITE_TAC[C2_TWO_POW_NEG2_COMPLEX_NORM];
    ALL_TAC] THEN
  SUBGOAL_THEN `c2_two_pow_real sigma - &1 <= norm(u - Cx(&1))`
  ASSUME_TAC THENL
   [MP_TAC(SPECL [`u:complex`; `--Cx(&1)`] COMPLEX_NORM_TRIANGLE_SUB) THEN
    REWRITE_TAC[complex_sub; COMPLEX_NORM_NEG; COMPLEX_NORM_CX;
                REAL_ABS_NUM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[COMPLEX_NORM_MUL] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[REAL_EXP_POS_LE]);;

let C2_C0_COMPLEX_DENOM_NORM_UPPER = prove
 (`!sigma t.
      norm(Cx(&2) * c2_two_pow_complex sigma t - Cx(&1))
      <= &2 * c2_two_pow_real sigma + &1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[complex_sub] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `norm(Cx(&2) * c2_two_pow_complex sigma t) + norm(--Cx(&1))` THEN
  CONJ_TAC THENL
   [MATCH_ACCEPT_TAC COMPLEX_NORM_TRIANGLE;
    REWRITE_TAC[COMPLEX_NORM_MUL; COMPLEX_NORM_NEG; COMPLEX_NORM_CX;
                REAL_ABS_NUM; C2_TWO_POW_COMPLEX_NORM] THEN
    REAL_ARITH_TAC]);;

let C2_C0_COMPLEX_NORM_GE_OFFAXIS_LOWER = prove
 (`!sigma t.
      &0 < sigma
      ==> c2_c0_offaxis_lower sigma <= norm(c2_c0_complex sigma t)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `u = c2_two_pow_complex sigma t` THEN
  ABBREV_TAC `a = c2_two_pow_neg2_complex sigma t` THEN
  ABBREV_TAC `d = norm(Cx(&2) * u - Cx(&1))` THEN
  SUBGOAL_THEN `&0 < d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN EXPAND_TAC "u" THEN
    MATCH_MP_TAC C2_C0_COMPLEX_DENOM_NORM_POS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `d <= &2 * c2_two_pow_real sigma + &1`
  ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN EXPAND_TAC "u" THEN
    REWRITE_TAC[C2_C0_COMPLEX_DENOM_NORM_UPPER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `c2_c0_offaxis_lower sigma * d <=
    exp(--(&2 * sigma * ln(&2))) * (c2_two_pow_real sigma - &1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC C2_C0_OFFAXIS_LOWER_SCALE_BOUND THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `exp(--(&2 * sigma * ln(&2))) * (c2_two_pow_real sigma - &1)
    <= norm(a * (u - Cx(&1)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN EXPAND_TAC "u" THEN
    MATCH_MP_TAC C2_C0_COMPLEX_NUMERATOR_NORM_LOWER THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `norm(c2_c0_complex sigma t) = norm(a * (u - Cx(&1))) / d`
  SUBST1_TAC THENL
   [REWRITE_TAC[c2_c0_complex; complex_div; COMPLEX_NORM_MUL;
                COMPLEX_NORM_INV; real_div; REAL_MUL_ASSOC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `exp(--(&2 * sigma * ln(&2))) *
              (c2_two_pow_real sigma - &1)` THEN
  ASM_REWRITE_TAC[]);;

let C2_C0_COMPLEX_REALIZES_OFFAXIS_PROFILE = prove
 (`c2_c0_offaxis_profile_realized c2_c0_complex`,
  REWRITE_TAC[c2_c0_offaxis_profile_realized;
              C2_C0_COMPLEX_NORM_GE_OFFAXIS_LOWER]);;

let C2_C0_COMPLEX_REALIZES_CRITICAL_PROFILE = prove
 (`c2_c0_critical_profile_realized (\t. c2_c0_complex (&1 / &2) t)`,
  REWRITE_TAC[c2_c0_critical_profile_realized; c2_c0_critical_lower] THEN
  GEN_TAC THEN
  MATCH_MP_TAC C2_C0_COMPLEX_NORM_GE_OFFAXIS_LOWER THEN
  REAL_ARITH_TAC);;

let C2_C0_COMPLEX_TRANSFER_CANONICAL = prove
 (`!zeta X C B sigma t.
      &0 < sigma /\ &0 < X /\
      abs(C) <= B * c2_c0_offaxis_lower sigma * X
      ==> norm(c2_zx zeta (c2_finite_residual_canonical X C)
               (c2_c0_complex sigma t) - zeta) <= B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C2_C0_OFFAXIS_PROFILE_TRANSFER_CANONICAL THEN
  ASM_REWRITE_TAC[C2_C0_COMPLEX_REALIZES_OFFAXIS_PROFILE]);;

let C2_C0_COMPLEX_TRANSFER = prove
 (`!zeta X C theta B sigma t.
      &0 < sigma /\ &0 < X /\ norm(theta) <= &1 /\
      abs(C) <= B * c2_c0_offaxis_lower sigma * X
      ==> norm(c2_zx zeta (c2_finite_residual X C theta)
               (c2_c0_complex sigma t) - zeta) <= B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C2_C0_OFFAXIS_PROFILE_TRANSFER THEN
  ASM_REWRITE_TAC[C2_C0_COMPLEX_REALIZES_OFFAXIS_PROFILE]);;
