(* ------------------------------------------------------------------------- *)
(* C2 route K: exact identity/continuation interface for Z_spec.             *)
(*                                                                           *)
(* Lean references:                                                          *)
(*   formal/lean_c2/LeanC2/Identity.lean                                     *)
(*   formal/lean_c2/LeanC2/Continuation.lean                                 *)
(*                                                                           *)
(* This HOL layer does not prove the analytic identity principle itself.     *)
(* Instead, it formalizes the exact quotient object                           *)
(*   Z_spec = (Dinf - Binf) / c0                                              *)
(* together with the algebraic consequences of a continued half-plane        *)
(* identity                                                                   *)
(*   Dinf - Binf = c0 * zeta                                                  *)
(* on sigma > 0. It also connects that interface to the multiplicity-safe    *)
(* transversal layer already formalized in HOL Light.                         *)
(* ------------------------------------------------------------------------- *)

prioritize_complex();;

let c2_thm13_identity = new_definition
 `c2_thm13_identity Dinf Binf c0 zeta <=>
    Dinf - Binf = c0 * zeta`;;

let c2_thm17_halfplane_eq = new_definition
 `(c2_thm17_halfplane_eq:
    (real->real->complex)->(real->real->complex)->bool) f g <=>
    !sigma t. &0 < sigma ==> f sigma t = g sigma t`;;

let c2_continuation_identity = new_definition
 `(c2_continuation_identity:
    (real->real->complex)->(real->real->complex)->
    (real->real->complex)->bool) Dinf Binf zeta <=>
    c2_thm17_halfplane_eq (\sigma t. Dinf sigma t - Binf sigma t)
                          (\sigma t. c2_c0_complex sigma t * zeta sigma t)`;;

let c2_zspec = new_definition
 `(c2_zspec:
    (real->real->complex)->(real->real->complex)->real->real->complex)
    Dinf Binf sigma t =
    (Dinf sigma t - Binf sigma t) / c2_c0_complex sigma t`;;

let C2_THM13_RATIO = prove
 (`!Dinf Binf c0 zeta.
      c2_thm13_identity Dinf Binf c0 zeta /\ ~(c0 = Cx(&0))
      ==> (Dinf - Binf) / c0 = zeta`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c2_thm13_identity] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(Dinf - Binf) / c0 = (c0 * zeta) / c0` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(c0 = Cx(&0)) ==> (c0 * zeta) / c0 = zeta` MP_TAC THENL
     [CONV_TAC COMPLEX_FIELD;
      ASM_REWRITE_TAC[]]]);;

let C2_THM17_OFFAXIS_EVAL = prove
 (`!(f:real->real->complex) g sigma t.
      c2_thm17_halfplane_eq f g /\ &0 < sigma
      ==> f sigma t = g sigma t`,
  REWRITE_TAC[c2_thm17_halfplane_eq] THEN
  MESON_TAC[]);;

let C2_CONTINUATION_IDENTITY_OFFAXIS = prove
 (`!(Dinf:real->real->complex) Binf zeta sigma t.
      c2_continuation_identity Dinf Binf zeta /\ &0 < sigma
      ==> Dinf sigma t - Binf sigma t =
          c2_c0_complex sigma t * zeta sigma t`,
  REWRITE_TAC[c2_continuation_identity; c2_thm17_halfplane_eq] THEN
  MESON_TAC[]);;

let C2_THM13_RATIO_OFFAXIS = prove
 (`!sigma t (Dinf:real->real->complex) Binf zeta.
      &0 < sigma /\
      Dinf sigma t - Binf sigma t =
      c2_c0_complex sigma t * zeta
      ==> c2_zspec Dinf Binf sigma t = zeta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[c2_zspec] THEN
  MATCH_MP_TAC C2_THM13_RATIO THEN
  ASM_REWRITE_TAC[c2_thm13_identity] THEN
  MATCH_MP_TAC C2_C0_COMPLEX_NONZERO THEN
  ASM_REWRITE_TAC[]);;

let C2_THM13_RATIO_CRITICAL = prove
 (`!t (Dinf:real->real->complex) Binf zeta.
      Dinf (&1 / &2) t - Binf (&1 / &2) t =
      c2_c0_complex (&1 / &2) t * zeta
      ==> c2_zspec Dinf Binf (&1 / &2) t = zeta`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC
   (SPECL [`&1 / &2`; `t:real`; `Dinf:real->real->complex`;
           `Binf:real->real->complex`; `zeta:complex`]
          C2_THM13_RATIO_OFFAXIS) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let C2_ZSPEC_EQ_OF_THM13 = prove
 (`!sigma t (Dinf:real->real->complex) Binf zeta.
      &0 < sigma /\
      Dinf sigma t - Binf sigma t =
      c2_c0_complex sigma t * zeta
      ==> c2_zspec Dinf Binf sigma t = zeta`,
  MESON_TAC[C2_THM13_RATIO_OFFAXIS]);;

let C2_ZSPEC_EQ_OF_CONTINUATION = prove
 (`!(Dinf:real->real->complex) Binf zeta sigma t.
      c2_continuation_identity Dinf Binf zeta /\ &0 < sigma
      ==> c2_zspec Dinf Binf sigma t = zeta sigma t`,
  MESON_TAC[C2_CONTINUATION_IDENTITY_OFFAXIS; C2_ZSPEC_EQ_OF_THM13]);;

let C2_CONTINUATION_ZERO_IFF = prove
 (`!(Dinf:real->real->complex) Binf zeta sigma t.
      c2_continuation_identity Dinf Binf zeta /\ &0 < sigma
      ==> (c2_zspec Dinf Binf sigma t = Cx(&0) <=>
           zeta sigma t = Cx(&0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `c2_zspec Dinf Binf sigma t = zeta sigma t` SUBST1_TAC THENL
   [MATCH_MP_TAC C2_ZSPEC_EQ_OF_CONTINUATION THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[]]);;

let C2_CONTINUATION_NONZERO_IFF_ZETA_NONZERO = prove
 (`!(Dinf:real->real->complex) Binf zeta sigma t.
      c2_continuation_identity Dinf Binf zeta /\ &0 < sigma
      ==> (~(Dinf sigma t - Binf sigma t = Cx(&0)) <=>
           ~(zeta sigma t = Cx(&0)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `Dinf sigma t - Binf sigma t =
    c2_c0_complex sigma t * zeta sigma t`
  ASSUME_TAC THENL
   [MATCH_MP_TAC C2_CONTINUATION_IDENTITY_OFFAXIS THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(c2_c0_complex sigma t = Cx(&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC C2_C0_COMPLEX_NONZERO THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[COMPLEX_ENTIRE] THEN MESON_TAC[]]);;

let C2_ZSPEC_NONZERO_OF_TRANSVERSAL_PRODUCT_JET = prove
 (`!(Dinf:real->real->complex) Binf sigma t m (w:num->complex)
     (cJet:num->complex) (zJet:num->complex).
      &0 < sigma /\
      w 0 = Cx(&1) /\
      (!k. k < m ==> zJet k = Cx(&0)) /\
      cJet 0 = c2_c0_complex sigma t /\
      ~(zJet m = Cx(&0)) /\
      c2_zspec Dinf Binf sigma t = c2_leibniz_sum m w cJet zJet
      ==> ~(c2_zspec Dinf Binf sigma t = Cx(&0))`,
  MESON_TAC[C2_THM8_TRANSVERSAL_PRODUCT_JET]);;

let C2_ZSPEC_NONZERO_OF_TRANSVERSAL_PRODUCT_JET_CRITICAL = prove
 (`!(Dinf:real->real->complex) Binf t m (w:num->complex)
     (cJet:num->complex) (zJet:num->complex).
      w 0 = Cx(&1) /\
      (!k. k < m ==> zJet k = Cx(&0)) /\
      cJet 0 = c2_c0_complex (&1 / &2) t /\
      ~(zJet m = Cx(&0)) /\
      c2_zspec Dinf Binf (&1 / &2) t = c2_leibniz_sum m w cJet zJet
      ==> ~(c2_zspec Dinf Binf (&1 / &2) t = Cx(&0))`,
  MESON_TAC[C2_THM8_TRANSVERSAL_PRODUCT_JET_CRITICAL]);;

let C2_GLOBAL_ZERO_EXCLUSION_OF_ZSPEC_NONVANISHING = prove
 (`!(Dinf:real->real->complex) Binf zeta.
      c2_continuation_identity Dinf Binf zeta /\
      (!sigma t.
          &0 < sigma /\ sigma < &1 /\ ~(sigma = &1 / &2)
          ==> ~(c2_zspec Dinf Binf sigma t = Cx(&0)))
      ==> !sigma t.
            &0 < sigma /\ sigma < &1 /\ ~(sigma = &1 / &2)
            ==> ~(zeta sigma t = Cx(&0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  X_GEN_TAC `sigma:real` THEN
  X_GEN_TAC `t:real` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `c2_zspec Dinf Binf sigma t = zeta sigma t` ASSUME_TAC THENL
   [MATCH_MP_TAC C2_ZSPEC_EQ_OF_CONTINUATION THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `~(c2_zspec Dinf Binf sigma t = Cx(&0))` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`sigma:real`; `t:real`]) THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]]]);;

let C2_GLOBAL_ZERO_EXCLUSION_OF_ZSPEC_TRANSVERSAL_PRODUCT_JET = prove
 (`!(Dinf:real->real->complex) Binf zeta.
      c2_continuation_identity Dinf Binf zeta /\
      (!sigma t.
          &0 < sigma /\ sigma < &1 /\ ~(sigma = &1 / &2)
          ==> ?m (w:num->complex) (cJet:num->complex) (zJet:num->complex).
                w 0 = Cx(&1) /\
                (!k. k < m ==> zJet k = Cx(&0)) /\
                cJet 0 = c2_c0_complex sigma t /\
                ~(zJet m = Cx(&0)) /\
                c2_zspec Dinf Binf sigma t = c2_leibniz_sum m w cJet zJet)
      ==> !sigma t.
            &0 < sigma /\ sigma < &1 /\ ~(sigma = &1 / &2)
            ==> ~(zeta sigma t = Cx(&0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  X_GEN_TAC `sigma:real` THEN
  X_GEN_TAC `t:real` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`sigma:real`; `t:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->complex` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `cJet:num->complex` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `zJet:num->complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(c2_zspec Dinf Binf sigma t = Cx(&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC C2_ZSPEC_NONZERO_OF_TRANSVERSAL_PRODUCT_JET THEN
    EXISTS_TAC `m:num` THEN
    EXISTS_TAC `w:num->complex` THEN
    EXISTS_TAC `cJet:num->complex` THEN
    EXISTS_TAC `zJet:num->complex` THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `c2_zspec Dinf Binf sigma t = Cx(&0)` MP_TAC THENL
     [MP_TAC
       (SPECL [`Dinf:real->real->complex`; `Binf:real->real->complex`;
               `zeta:real->real->complex`; `sigma:real`; `t:real`]
              C2_CONTINUATION_ZERO_IFF) THEN
      ASM_REWRITE_TAC[] THEN
      MESON_TAC[];
      ASM_REWRITE_TAC[]]]);;

let C2_GLOBAL_ZERO_EXCLUSION_OF_CONTINUATION_PRODUCT_JET = prove
 (`!(Dinf:real->real->complex) Binf zeta.
      c2_continuation_identity Dinf Binf zeta /\
      (!sigma t.
          &0 < sigma /\ sigma < &1 /\ ~(sigma = &1 / &2)
          ==> ?m (w:num->complex) (cJet:num->complex) (zJet:num->complex).
                w 0 = Cx(&1) /\
                (!k. k < m ==> zJet k = Cx(&0)) /\
                cJet 0 = c2_c0_complex sigma t /\
                ~(zJet m = Cx(&0)) /\
                c2_c0_complex sigma t * zeta sigma t =
                c2_leibniz_sum m w cJet zJet)
      ==> !sigma t.
            &0 < sigma /\ sigma < &1 /\ ~(sigma = &1 / &2)
            ==> ~(zeta sigma t = Cx(&0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  X_GEN_TAC `sigma:real` THEN
  X_GEN_TAC `t:real` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`sigma:real`; `t:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->complex` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `cJet:num->complex` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `zJet:num->complex` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(c2_c0_complex sigma t * zeta sigma t = Cx(&0))` ASSUME_TAC THENL
   [MATCH_MP_TAC
     (SPECL [`sigma:real`; `t:real`; `m:num`; `w:num->complex`;
             `cJet:num->complex`; `zJet:num->complex`;
             `c2_c0_complex sigma t * zeta sigma t`]
            C2_THM8_TRANSVERSAL_PRODUCT_JET) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC
      (TAUT
        `~((c2_c0_complex sigma t = Cx(&0)) \/
           (zeta sigma t = Cx(&0)))
         ==> ~(zeta sigma t = Cx(&0))`) THEN
    UNDISCH_TAC `~(c2_c0_complex sigma t * zeta sigma t = Cx(&0))` THEN
    ASM_REWRITE_TAC[COMPLEX_ENTIRE]]);;

let C2_GLOBAL_ZERO_EXCLUSION_OF_NUMERATOR_TRANSVERSAL_PRODUCT_JET = prove
 (`!(Dinf:real->real->complex) Binf zeta.
      c2_continuation_identity Dinf Binf zeta /\
      (!sigma t.
          &0 < sigma /\ sigma < &1 /\ ~(sigma = &1 / &2)
          ==> ?m (w:num->complex) (cJet:num->complex) (zJet:num->complex).
                w 0 = Cx(&1) /\
                (!k. k < m ==> zJet k = Cx(&0)) /\
                cJet 0 = c2_c0_complex sigma t /\
                ~(zJet m = Cx(&0)) /\
                Dinf sigma t - Binf sigma t = c2_leibniz_sum m w cJet zJet)
      ==> !sigma t.
            &0 < sigma /\ sigma < &1 /\ ~(sigma = &1 / &2)
            ==> ~(zeta sigma t = Cx(&0))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC
    (SPECL [`Dinf:real->real->complex`; `Binf:real->real->complex`;
            `zeta:real->real->complex`]
           C2_GLOBAL_ZERO_EXCLUSION_OF_CONTINUATION_PRODUCT_JET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `sigma:real` THEN
  X_GEN_TAC `t:real` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`sigma:real`; `t:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num->complex` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `cJet:num->complex` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `zJet:num->complex` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `m:num` THEN
  EXISTS_TAC `w:num->complex` THEN
  EXISTS_TAC `cJet:num->complex` THEN
  EXISTS_TAC `zJet:num->complex` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC
    (SPECL [`Dinf:real->real->complex`; `Binf:real->real->complex`;
            `zeta:real->real->complex`; `sigma:real`; `t:real`]
           C2_CONTINUATION_IDENTITY_OFFAXIS) THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[]);;
