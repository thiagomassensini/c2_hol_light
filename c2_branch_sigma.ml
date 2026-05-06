(* ------------------------------------------------------------------------- *)
(* C2 route K: sigma bridge for the branch-operator barrier.                 *)
(*                                                                           *)
(* Lean reference: formal/lean_c2/LeanC2/Barrier.lean, qOfSigma section.      *)
(*                                                                           *)
(* HOL Light's real transcendental library uses ln for the real logarithm.    *)
(* This module connects the already-proved q-barrier to sigma by setting      *)
(* q(sigma) = exp(-(2 sigma) ln 2).                                           *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let c2_q_of_sigma = new_definition
 `c2_q_of_sigma sigma = exp(--(&2 * sigma * ln(&2)))`;;

let c2_branch_mass_sigma_t = new_definition
 `c2_branch_mass_sigma_t (sigma:real) (t:real) =
    c2_branch_mass (c2_q_of_sigma sigma)`;;

let C2_LN2_POS = prove
 (`&0 < ln(&2)`,
  MATCH_MP_TAC LN_POS_LT THEN REAL_ARITH_TAC);;

let C2_NEG_TWO_LN_MONO_LT = prove
 (`!a b L. &0 < L
           ==> (--(&2 * a * L) < --(&2 * b * L) <=> b < a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &2 * L` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `--x < --y <=> y < x`] THEN
  SUBGOAL_THEN `&2 * b * L = b * (&2 * L)` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * a * L = a * (&2 * L)` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  MP_TAC(SPECL [`b:real`; `a:real`; `&2 * L`] REAL_LT_RMUL_EQ) THEN
  ASM_REWRITE_TAC[]);;

let C2_NEG_TWO_LN_MONO_EQ = prove
 (`!a b L. &0 < L
           ==> (--(&2 * a * L) = --(&2 * b * L) <=> a = b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(&2 * L = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_IMP_NZ THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(--x = --y) <=> (x = y)`] THEN
  SUBGOAL_THEN `&2 * a * L = a * (&2 * L)` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * b * L = b * (&2 * L)` SUBST1_TAC THENL
   [CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(c = &0) ==> (a * c = b * c <=> a = b)`]);;

let C2_Q_OF_SIGMA_POS_LT = prove
 (`!sigma. &0 < c2_q_of_sigma sigma`,
  REWRITE_TAC[c2_q_of_sigma; REAL_EXP_POS_LT]);;

let C2_Q_OF_SIGMA_NONNEG = prove
 (`!sigma. &0 <= c2_q_of_sigma sigma`,
  MESON_TAC[C2_Q_OF_SIGMA_POS_LT; REAL_LT_IMP_LE]);;

let C2_Q_OF_SIGMA_LT_ONE_IFF = prove
 (`!sigma. c2_q_of_sigma sigma < &1 <=> &0 < sigma`,
  GEN_TAC THEN
  REWRITE_TAC[c2_q_of_sigma; GSYM REAL_EXP_0; REAL_EXP_MONO_LT] THEN
  MP_TAC(SPECL [`sigma:real`; `&0`; `ln(&2)`]
         C2_NEG_TWO_LN_MONO_LT) THEN
  REWRITE_TAC[C2_LN2_POS] THEN REAL_ARITH_TAC);;

let C2_Q_OF_SIGMA_HALF = prove
 (`c2_q_of_sigma (&1 / &2) = &1 / &2`,
  REWRITE_TAC[c2_q_of_sigma] THEN
  SUBGOAL_THEN `--(&2 * (&1 / &2) * ln(&2)) = --ln(&2)`
   SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  REWRITE_TAC[REAL_EXP_NEG] THEN
  SUBGOAL_THEN `exp(ln(&2)) = &2` SUBST1_TAC THENL
   [MATCH_MP_TAC EXP_LN THEN REAL_ARITH_TAC;
    CONV_TAC REAL_RAT_REDUCE_CONV]);;

let C2_Q_OF_SIGMA_LT_HALF_IFF = prove
 (`!sigma. c2_q_of_sigma sigma < &1 / &2 <=> &1 / &2 < sigma`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM C2_Q_OF_SIGMA_HALF] THEN
  REWRITE_TAC[c2_q_of_sigma; REAL_EXP_MONO_LT] THEN
  MP_TAC(SPECL [`sigma:real`; `&1 / &2`; `ln(&2)`]
         C2_NEG_TWO_LN_MONO_LT) THEN
  REWRITE_TAC[C2_LN2_POS] THEN
  DISCH_THEN ACCEPT_TAC);;

let C2_Q_OF_SIGMA_GT_HALF_IFF = prove
 (`!sigma. &1 / &2 < c2_q_of_sigma sigma <=> sigma < &1 / &2`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM C2_Q_OF_SIGMA_HALF] THEN
  REWRITE_TAC[c2_q_of_sigma; REAL_EXP_MONO_LT] THEN
  MP_TAC(SPECL [`&1 / &2`; `sigma:real`; `ln(&2)`]
         C2_NEG_TWO_LN_MONO_LT) THEN
  REWRITE_TAC[C2_LN2_POS] THEN
  DISCH_THEN ACCEPT_TAC);;

let C2_Q_OF_SIGMA_EQ_HALF_IFF = prove
 (`!sigma. c2_q_of_sigma sigma = &1 / &2 <=> sigma = &1 / &2`,
  GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM C2_Q_OF_SIGMA_HALF] THEN
  REWRITE_TAC[c2_q_of_sigma; REAL_EXP_INJ] THEN
  MP_TAC(SPECL [`sigma:real`; `&1 / &2`; `ln(&2)`]
         C2_NEG_TWO_LN_MONO_EQ) THEN
  REWRITE_TAC[C2_LN2_POS] THEN
  DISCH_THEN ACCEPT_TAC);;

let C2_BRANCH_MASS_SIGMA_LT_ONE_IFF = prove
 (`!sigma. &0 < sigma
           ==> (c2_branch_mass (c2_q_of_sigma sigma) < &1 <=>
                &1 / &2 < sigma)`,
  ASM_MESON_TAC[C2_BRANCH_MASS_LT_ONE_IFF;
                C2_Q_OF_SIGMA_NONNEG;
                C2_Q_OF_SIGMA_LT_ONE_IFF;
                C2_Q_OF_SIGMA_LT_HALF_IFF]);;

let C2_BRANCH_MASS_SIGMA_EQ_ONE_IFF = prove
 (`!sigma. &0 < sigma
           ==> (c2_branch_mass (c2_q_of_sigma sigma) = &1 <=>
                sigma = &1 / &2)`,
  ASM_MESON_TAC[C2_BRANCH_MASS_EQ_ONE_IFF;
                C2_Q_OF_SIGMA_NONNEG;
                C2_Q_OF_SIGMA_LT_ONE_IFF;
                C2_Q_OF_SIGMA_EQ_HALF_IFF]);;

let C2_BRANCH_MASS_SIGMA_GT_ONE_IFF = prove
 (`!sigma. &0 < sigma
           ==> (&1 < c2_branch_mass (c2_q_of_sigma sigma) <=>
                sigma < &1 / &2)`,
  ASM_MESON_TAC[C2_BRANCH_MASS_GT_ONE_IFF;
                C2_Q_OF_SIGMA_NONNEG;
                C2_Q_OF_SIGMA_LT_ONE_IFF;
                C2_Q_OF_SIGMA_GT_HALF_IFF]);;

let C2_BRANCH_MASS_SIGMA_T_INDEPENDENT_OF_T = prove
 (`!sigma t1 t2.
      c2_branch_mass_sigma_t sigma t1 =
      c2_branch_mass_sigma_t sigma t2`,
  REWRITE_TAC[c2_branch_mass_sigma_t]);;

let C2_BRANCH_BARRIER_SIGMA_TRICHOTOMY = prove
 (`!sigma t. &0 < sigma
             ==> (c2_branch_mass_sigma_t sigma t < &1 <=>
                  &1 / &2 < sigma) /\
                 (c2_branch_mass_sigma_t sigma t = &1 <=>
                  sigma = &1 / &2) /\
                 (&1 < c2_branch_mass_sigma_t sigma t <=>
                  sigma < &1 / &2)`,
  REWRITE_TAC[c2_branch_mass_sigma_t] THEN
  MESON_TAC[C2_BRANCH_MASS_SIGMA_LT_ONE_IFF;
            C2_BRANCH_MASS_SIGMA_EQ_ONE_IFF;
            C2_BRANCH_MASS_SIGMA_GT_ONE_IFF]);;
