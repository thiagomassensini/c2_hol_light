(* ------------------------------------------------------------------------- *)
(* C2 route K: bridge from branch barrier to genuine transfer operator.       *)
(*                                                                           *)
(* Lean reference:                                                           *)
(*   formal/lean_c2/LeanC2/OperatorNorm.lean                                 *)
(*   formal/lean_c2/LeanC2/Transfer.lean                                      *)
(*   formal/lean_c2/LeanC2/Chain.lean                                         *)
(*                                                                           *)
(* This HOL layer formalizes the norm-level bridge used by the Lean theorem   *)
(* routeK_bridge_branch_to_genuine_*: the branch barrier and the genuine      *)
(* transfer estimate hold simultaneously once the residual is controlled by   *)
(* a positive lower bound L <= ||c0||.                                        *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let c2_branch_norm_sq = new_definition
 `c2_branch_norm_sq sigma = c2_branch_mass (c2_q_of_sigma sigma)`;;

let c2_branch_norm_sq_sigma_t = new_definition
 `c2_branch_norm_sq_sigma_t (sigma:real) (t:real) =
    c2_branch_norm_sq sigma`;;

let c2_genuine_transfer_error = new_definition
 `c2_genuine_transfer_error residual_norm c0_norm =
    residual_norm / c0_norm`;;

let C2_BRANCH_NORM_SQ_HALF = prove
 (`c2_branch_norm_sq (&1 / &2) = &1`,
  REWRITE_TAC[c2_branch_norm_sq; C2_Q_OF_SIGMA_HALF; C2_BRANCH_MASS_HALF]);;

let C2_BRANCH_NORM_SQ_SIGMA_T_INDEPENDENT_OF_T = prove
 (`!sigma t1 t2.
      c2_branch_norm_sq_sigma_t sigma t1 =
      c2_branch_norm_sq_sigma_t sigma t2`,
  REWRITE_TAC[c2_branch_norm_sq_sigma_t]);;

let C2_BRANCH_NORM_SQ_LT_ONE_IFF = prove
 (`!sigma. &0 < sigma
           ==> (c2_branch_norm_sq sigma < &1 <=> &1 / &2 < sigma)`,
  REWRITE_TAC[c2_branch_norm_sq] THEN
  MESON_TAC[C2_BRANCH_MASS_SIGMA_LT_ONE_IFF]);;

let C2_BRANCH_NORM_SQ_EQ_ONE_IFF = prove
 (`!sigma. &0 < sigma
           ==> (c2_branch_norm_sq sigma = &1 <=> sigma = &1 / &2)`,
  REWRITE_TAC[c2_branch_norm_sq] THEN
  MESON_TAC[C2_BRANCH_MASS_SIGMA_EQ_ONE_IFF]);;

let C2_BRANCH_NORM_SQ_GT_ONE_IFF = prove
 (`!sigma. &0 < sigma
           ==> (&1 < c2_branch_norm_sq sigma <=> sigma < &1 / &2)`,
  REWRITE_TAC[c2_branch_norm_sq] THEN
  MESON_TAC[C2_BRANCH_MASS_SIGMA_GT_ONE_IFF]);;

let C2_BRANCH_NORM_SQ_SIGMA_T_TRICHOTOMY = prove
 (`!sigma t. &0 < sigma
             ==> (c2_branch_norm_sq_sigma_t sigma t < &1 <=>
                  &1 / &2 < sigma) /\
                 (c2_branch_norm_sq_sigma_t sigma t = &1 <=>
                  sigma = &1 / &2) /\
                 (&1 < c2_branch_norm_sq_sigma_t sigma t <=>
                  sigma < &1 / &2)`,
  REWRITE_TAC[c2_branch_norm_sq_sigma_t] THEN
  MESON_TAC[C2_BRANCH_NORM_SQ_LT_ONE_IFF;
            C2_BRANCH_NORM_SQ_EQ_ONE_IFF;
            C2_BRANCH_NORM_SQ_GT_ONE_IFF]);;

let C2_GENUINE_TRANSFER_BOUND = prove
 (`!residual_norm c0_norm L B.
      &0 <= residual_norm /\ &0 < L /\ L <= c0_norm /\
      residual_norm <= B * L
      ==> c2_genuine_transfer_error residual_norm c0_norm <= B`,
  REWRITE_TAC[c2_genuine_transfer_error] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < c0_norm` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
  SUBGOAL_THEN `&0 <= B` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= B * L` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`&0`; `B:real`; `L:real`] REAL_LE_RMUL_EQ) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `B * L` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_REWRITE_TAC[]);;

let C2_BRIDGE_BRANCH_TO_GENUINE_CRITICAL = prove
 (`!t residual_norm c0_norm L B.
      &0 <= residual_norm /\ &0 < L /\ L <= c0_norm /\
      residual_norm <= B * L
      ==> c2_branch_norm_sq_sigma_t (&1 / &2) t = &1 /\
          c2_genuine_transfer_error residual_norm c0_norm <= B`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[c2_branch_norm_sq_sigma_t; C2_BRANCH_NORM_SQ_HALF] THEN
  MATCH_MP_TAC C2_GENUINE_TRANSFER_BOUND THEN
  EXISTS_TAC `L:real` THEN
  ASM_REWRITE_TAC[]);;

let C2_BRIDGE_BRANCH_TO_GENUINE_OFFAXIS = prove
 (`!sigma t residual_norm c0_norm L B.
      &0 < sigma /\ &1 / &2 < sigma /\
      &0 <= residual_norm /\ &0 < L /\ L <= c0_norm /\
      residual_norm <= B * L
      ==> c2_branch_norm_sq_sigma_t sigma t < &1 /\
          c2_genuine_transfer_error residual_norm c0_norm <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[c2_branch_norm_sq_sigma_t] THEN
    ASM_MESON_TAC[C2_BRANCH_NORM_SQ_LT_ONE_IFF];
    MATCH_MP_TAC C2_GENUINE_TRANSFER_BOUND THEN
    EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[]]);;

let C2_BRIDGE_BRANCH_TO_GENUINE_OFFAXIS_EXPANSIVE_SIDE = prove
 (`!sigma t residual_norm c0_norm L B.
      &0 < sigma /\ sigma < &1 / &2 /\
      &0 <= residual_norm /\ &0 < L /\ L <= c0_norm /\
      residual_norm <= B * L
      ==> &1 < c2_branch_norm_sq_sigma_t sigma t /\
          c2_genuine_transfer_error residual_norm c0_norm <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[c2_branch_norm_sq_sigma_t] THEN
    ASM_MESON_TAC[C2_BRANCH_NORM_SQ_GT_ONE_IFF];
    MATCH_MP_TAC C2_GENUINE_TRANSFER_BOUND THEN
    EXISTS_TAC `L:real` THEN
    ASM_REWRITE_TAC[]]);;
