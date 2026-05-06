(* ------------------------------------------------------------------------- *)
(* C2 route K: branch-operator barrier, HOL Light port.                      *)
(*                                                                           *)
(* Lean reference: formal/lean_c2/LeanC2/Barrier.lean                         *)
(* Paper reference: branch-operator barrier / C2 selectivity section.         *)
(*                                                                           *)
(* This first HOL layer formalizes the algebraic branch-parameter barrier.    *)
(* The sigma -> q transcendental bridge is intentionally left for the next     *)
(* module; here q is the positive branch ratio.                               *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let c2_branch_mass = new_definition
 `c2_branch_mass q = (&2 * q pow 2) / (&1 - q)`;;

let c2_branch_mass_st = new_definition
 `c2_branch_mass_st (sigma:real) (t:real) q = c2_branch_mass q`;;

let C2_BRANCH_MASS_ST_INDEPENDENT_OF_T = prove
 (`!sigma t1 t2 q.
        c2_branch_mass_st sigma t1 q = c2_branch_mass_st sigma t2 q`,
  REWRITE_TAC[c2_branch_mass_st]);;

let C2_BRANCH_MASS_HALF = prove
 (`c2_branch_mass (&1 / &2) = &1`,
  REWRITE_TAC[c2_branch_mass] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

let C2_BRANCH_MASS_DENOM_POS = prove
 (`!q. q < &1 ==> &0 < &1 - q`,
  REAL_ARITH_TAC);;

let C2_BRANCH_POLY_LT = prove
 (`!q. &0 <= q ==> (&2 * q pow 2 < &1 - q <=> q < &1 / &2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < q + &1` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a < b <=> a - b < &0`] THEN
  SUBGOAL_THEN
   `&2 * q * q - (&1 - q) = (&2 * q - &1) * (q + &1)`
   SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `((&2 * q - &1) * (q + &1) < &0 <=>
     &2 * q - &1 < &0)`
   ASSUME_TAC THENL
   [MP_TAC(SPECL [`&2 * q - &1`; `&0`; `q + &1`]
          REAL_LT_RMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO];
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let C2_BRANCH_POLY_EQ = prove
 (`!q. &0 <= q ==> (&2 * q pow 2 = &1 - q <=> q = &1 / &2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(q + &1 = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a = b <=> a - b = &0`] THEN
  SUBGOAL_THEN
   `&2 * q * q - (&1 - q) = (&2 * q - &1) * (q + &1)`
   SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  ASM_REWRITE_TAC[REAL_ENTIRE] THEN
  REAL_ARITH_TAC);;

let C2_BRANCH_POLY_GT = prove
 (`!q. &0 <= q ==> (&1 - q < &2 * q pow 2 <=> &1 / &2 < q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < q + &1` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[REAL_POW_2] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a < b <=> &0 < b - a`] THEN
  SUBGOAL_THEN
   `&2 * q * q - (&1 - q) = (&2 * q - &1) * (q + &1)`
   SUBST1_TAC THENL [CONV_TAC REAL_RING; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&0 < (&2 * q - &1) * (q + &1) <=>
     &0 < &2 * q - &1)`
   ASSUME_TAC THENL
   [MP_TAC(SPECL [`&0`; `&2 * q - &1`; `q + &1`]
          REAL_LT_RMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO];
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

let C2_BRANCH_MASS_LT_POLY = prove
 (`!q. q < &1
       ==> (c2_branch_mass q < &1 <=> &2 * q pow 2 < &1 - q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - q` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[c2_branch_mass; REAL_LT_LDIV_EQ; REAL_MUL_LID]);;

let C2_BRANCH_MASS_EQ_POLY = prove
 (`!q. q < &1
       ==> (c2_branch_mass q = &1 <=> &2 * q pow 2 = &1 - q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - q` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[c2_branch_mass; REAL_EQ_LDIV_EQ; REAL_MUL_LID]);;

let C2_BRANCH_MASS_GT_POLY = prove
 (`!q. q < &1
       ==> (&1 < c2_branch_mass q <=> &1 - q < &2 * q pow 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - q` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[c2_branch_mass; REAL_LT_RDIV_EQ; REAL_MUL_LID]);;

let C2_BRANCH_MASS_LT_ONE_IFF = prove
 (`!q. &0 <= q /\ q < &1
       ==> (c2_branch_mass q < &1 <=> q < &1 / &2)`,
  ASM_MESON_TAC[C2_BRANCH_MASS_LT_POLY; C2_BRANCH_POLY_LT]);;

let C2_BRANCH_MASS_EQ_ONE_IFF = prove
 (`!q. &0 <= q /\ q < &1
       ==> (c2_branch_mass q = &1 <=> q = &1 / &2)`,
  ASM_MESON_TAC[C2_BRANCH_MASS_EQ_POLY; C2_BRANCH_POLY_EQ]);;

let C2_BRANCH_MASS_GT_ONE_IFF = prove
 (`!q. &0 <= q /\ q < &1
       ==> (&1 < c2_branch_mass q <=> &1 / &2 < q)`,
  ASM_MESON_TAC[C2_BRANCH_MASS_GT_POLY; C2_BRANCH_POLY_GT]);;

let C2_BRANCH_BARRIER_TRICHOTOMY = prove
 (`!q. &0 <= q /\ q < &1
       ==> (c2_branch_mass q < &1 <=> q < &1 / &2) /\
           (c2_branch_mass q = &1 <=> q = &1 / &2) /\
           (&1 < c2_branch_mass q <=> &1 / &2 < q)`,
  MESON_TAC[C2_BRANCH_MASS_LT_ONE_IFF;
            C2_BRANCH_MASS_EQ_ONE_IFF;
            C2_BRANCH_MASS_GT_ONE_IFF]);;

(* This is the formal HOL statement of the t-blind part of the branch channel:
   once the real branch ratio q is fixed, the branch mass sees no imaginary
   coordinate. *)
let C2_BRANCH_BARRIER_T_BLIND = prove
 (`!sigma t1 t2 q.
        c2_branch_mass_st sigma t1 q = c2_branch_mass_st sigma t2 q`,
  REWRITE_TAC[c2_branch_mass_st]);;
