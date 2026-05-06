(* ------------------------------------------------------------------------- *)
(* C2 route K: Thm 8 as multiplicity-safe Leibniz transversality.            *)
(*                                                                           *)
(* Lean references:                                                          *)
(*   formal/lean_c2/LeanC2/Tilt.lean                                         *)
(*   leibnizCollapseByMultiplicity                                            *)
(*   routeK_thm8_transversal_abstract                                         *)
(*   routeK_thm8_transversal_product_jet                                      *)
(*                                                                           *)
(* This layer formalizes the multiplicity-safe Leibniz collapse used in      *)
(* Rota K Thm 8. The only coefficient property that matters under the        *)
(* multiplicity hypothesis is that the j = 0 Leibniz weight equals 1.        *)
(* If the zeta jet vanishes up to order m-1 and the order-m jet is nonzero,  *)
(* then the order-m product jet collapses to c0*zeta^(m) and is therefore    *)
(* nonzero whenever c0 is nonzero.                                           *)
(* ------------------------------------------------------------------------- *)

prioritize_complex();;

let c2_complex_nsum = new_recursive_definition num_RECURSION
 `(c2_complex_nsum 0 f = f 0) /\
  (!n. c2_complex_nsum (SUC n) f = c2_complex_nsum n f + f (SUC n))`;;

let c2_leibniz_sum = new_definition
 `c2_leibniz_sum m w c z =
    c2_complex_nsum m (\j. w j * c j * z (m - j))`;;

let C2_COMPLEX_NSUM_ALL_ZERO_EXCEPT_0 = prove
 (`!m (f:num->complex).
      (!j. 1 <= j /\ j <= m ==> f j = Cx(&0))
      ==> c2_complex_nsum m f = f 0`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THENL
   [REWRITE_TAC[c2_complex_nsum];
    ASM_REWRITE_TAC[c2_complex_nsum] THEN
    SUBGOAL_THEN `f (SUC m) = Cx(&0)` SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC;
      REWRITE_TAC[COMPLEX_ADD_RID] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC]]);;

let C2_LEIBNIZ_COLLAPSE_BY_MULTIPLICITY = prove
 (`!m (w:num->complex) (c:num->complex) (z:num->complex).
      w 0 = Cx(&1) /\
      (!k. k < m ==> z k = Cx(&0))
      ==> c2_leibniz_sum m w c z = c 0 * z m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[c2_leibniz_sum] THEN
  MP_TAC
   (ISPECL [`m:num`; `\j:num. w j * c j * z (m - j)`]
           C2_COMPLEX_NSUM_ALL_ZERO_EXCEPT_0) THEN
  ANTS_TAC THENL
   [X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= j /\ j <= m ==> m - j < m`;
                 COMPLEX_MUL_RZERO; COMPLEX_MUL_LZERO];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[SUB_0; COMPLEX_MUL_LID]);;

let C2_LEIBNIZ_NONDEGENERATE_BY_MULTIPLICITY = prove
 (`!m (w:num->complex) (c:num->complex) (z:num->complex).
      w 0 = Cx(&1) /\
      (!k. k < m ==> z k = Cx(&0)) /\
      ~(c 0 = Cx(&0)) /\
      ~(z m = Cx(&0))
      ==> ~(c2_leibniz_sum m w c z = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c2_leibniz_sum m w c z = c 0 * z m` SUBST1_TAC THENL
   [MATCH_MP_TAC C2_LEIBNIZ_COLLAPSE_BY_MULTIPLICITY THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[COMPLEX_ENTIRE]]);;

let C2_C0_COMPLEX_NONZERO = prove
 (`!sigma t. &0 < sigma ==> ~(c2_c0_complex sigma t = Cx(&0))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `c2_c0_complex sigma t = Cx(&0)` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`sigma:real`; `t:real`] C2_C0_COMPLEX_NORM_GE_OFFAXIS_LOWER) THEN
  ASM_REWRITE_TAC[COMPLEX_NORM_0] THEN
  MP_TAC(SPEC `sigma:real` C2_C0_OFFAXIS_LOWER_POS) THEN
  ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let C2_THM8_TRANSVERSAL_ABSTRACT = prove
 (`!m (w:num->complex) (c:num->complex) (z:num->complex).
      w 0 = Cx(&1) /\
      (!k. k < m ==> z k = Cx(&0)) /\
      ~(c 0 = Cx(&0)) /\
      ~(z m = Cx(&0))
      ==> ~(c2_leibniz_sum m w c z = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C2_LEIBNIZ_NONDEGENERATE_BY_MULTIPLICITY THEN
  ASM_REWRITE_TAC[]);;

let C2_CHAIN_THM14_TO_THM8_ABSTRACT = prove
 (`!sigma t m (w:num->complex) (c:num->complex) (z:num->complex).
      &0 < sigma /\
      w 0 = Cx(&1) /\
      (!k. k < m ==> z k = Cx(&0)) /\
      c 0 = c2_c0_complex sigma t /\
      ~(z m = Cx(&0))
      ==> ~(c2_leibniz_sum m w c z = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(c 0 = Cx(&0))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC C2_C0_COMPLEX_NONZERO THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC C2_THM8_TRANSVERSAL_ABSTRACT THEN
    ASM_REWRITE_TAC[]]);;

let C2_CHAIN_THM14_TO_THM8_CRITICAL = prove
 (`!t m (w:num->complex) (c:num->complex) (z:num->complex).
      w 0 = Cx(&1) /\
      (!k. k < m ==> z k = Cx(&0)) /\
      c 0 = c2_c0_complex (&1 / &2) t /\
      ~(z m = Cx(&0))
      ==> ~(c2_leibniz_sum m w c z = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
   (SPECL [`&1 / &2`; `t:real`; `m:num`; `w:num->complex`;
           `c:num->complex`; `z:num->complex`]
          C2_CHAIN_THM14_TO_THM8_ABSTRACT) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let C2_THM8_TRANSVERSAL_PRODUCT_JET = prove
 (`!sigma t m (w:num->complex) (cJet:num->complex) (zJet:num->complex) Fjet.
      &0 < sigma /\
      w 0 = Cx(&1) /\
      (!k. k < m ==> zJet k = Cx(&0)) /\
      cJet 0 = c2_c0_complex sigma t /\
      ~(zJet m = Cx(&0)) /\
      Fjet = c2_leibniz_sum m w cJet zJet
      ==> ~(Fjet = Cx(&0))`,
  MESON_TAC[C2_CHAIN_THM14_TO_THM8_ABSTRACT]);;

let C2_THM8_TRANSVERSAL_PRODUCT_JET_CRITICAL = prove
 (`!t m (w:num->complex) (cJet:num->complex) (zJet:num->complex) Fjet.
      w 0 = Cx(&1) /\
      (!k. k < m ==> zJet k = Cx(&0)) /\
      cJet 0 = c2_c0_complex (&1 / &2) t /\
      ~(zJet m = Cx(&0)) /\
      Fjet = c2_leibniz_sum m w cJet zJet
      ==> ~(Fjet = Cx(&0))`,
  MESON_TAC[C2_CHAIN_THM14_TO_THM8_CRITICAL]);;

let C2_TRANSVERSAL_JET_NONZERO_OF_MULTIPLICITY = prove
 (`!m (w:num->complex) (c:num->complex) (z:num->complex).
      w 0 = Cx(&1) /\
      (!k. k < m ==> z k = Cx(&0)) /\
      ~(c 0 = Cx(&0)) /\
      ~(z m = Cx(&0))
      ==> ~(c2_leibniz_sum m w c z = Cx(&0))`,
  MESON_TAC[C2_LEIBNIZ_NONDEGENERATE_BY_MULTIPLICITY]);;

let C2_THM8_TRANSVERSAL_SIGMA_PRODUCT_JET = prove
 (`!sigma t m (w:num->complex) (cJet:num->complex) (zJet:num->complex) Fjet.
      &0 < sigma /\
      w 0 = Cx(&1) /\
      (!k. k < m ==> zJet k = Cx(&0)) /\
      cJet 0 = c2_c0_complex sigma t /\
      ~(zJet m = Cx(&0)) /\
      Fjet = c2_leibniz_sum m w cJet zJet
      ==> Fjet = c2_c0_complex sigma t * zJet m /\
          ~(Fjet = Cx(&0))`,
  MESON_TAC[C2_CHAIN_THM14_TO_THM8_ABSTRACT;
            C2_LEIBNIZ_COLLAPSE_BY_MULTIPLICITY]);;

let C2_THM8_TRANSVERSAL_SIGMA_PRODUCT_JET_CRITICAL = prove
 (`!t m (w:num->complex) (cJet:num->complex) (zJet:num->complex) Fjet.
      w 0 = Cx(&1) /\
      (!k. k < m ==> zJet k = Cx(&0)) /\
      cJet 0 = c2_c0_complex (&1 / &2) t /\
      ~(zJet m = Cx(&0)) /\
      Fjet = c2_leibniz_sum m w cJet zJet
      ==> Fjet = c2_c0_complex (&1 / &2) t * zJet m /\
          ~(Fjet = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC
   (SPECL [`&1 / &2`; `t:real`; `m:num`; `w:num->complex`;
           `cJet:num->complex`; `zJet:num->complex`; `Fjet:complex`]
          C2_THM8_TRANSVERSAL_SIGMA_PRODUCT_JET) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
