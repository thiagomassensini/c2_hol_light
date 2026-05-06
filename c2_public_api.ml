(* ------------------------------------------------------------------------- *)
(* C2 route K: stable public HOL Light interface mirroring the Lean surface. *)
(*                                                                           *)
(* This layer does not add new mathematics. It exposes descriptive theorem   *)
(* names for the endpoint-facing pieces that are already proved in the HOL   *)
(* modules below the implementation layer.                                    *)
(* ------------------------------------------------------------------------- *)

prioritize_complex();;

let C2_PUBLIC_C0_NONZERO_ON_RIGHT_HALFPLANE = prove
 (`!sigma t.
      &0 < sigma
      ==> ~(c2_c0_complex sigma t = Cx(&0))`,
  MESON_TAC[C2_C0_COMPLEX_NONZERO]);;

let C2_PUBLIC_C0_NONZERO_ON_CRITICAL_LINE = prove
 (`!t. ~(c2_c0_complex (&1 / &2) t = Cx(&0))`,
  GEN_TAC THEN
  MATCH_MP_TAC C2_C0_COMPLEX_NONZERO THEN
  REAL_ARITH_TAC);;

let C2_PUBLIC_ZSPEC_RATIO_OF_THM13_OFFAXIS = prove
 (`!sigma t (Dinf:real->real->complex) Binf zeta.
      &0 < sigma /\
      Dinf sigma t - Binf sigma t =
      c2_c0_complex sigma t * zeta
      ==> c2_zspec Dinf Binf sigma t = zeta`,
  MESON_TAC[C2_THM13_RATIO_OFFAXIS]);;

let C2_PUBLIC_ZSPEC_RATIO_OF_THM13_CRITICAL = prove
 (`!t (Dinf:real->real->complex) Binf zeta.
      Dinf (&1 / &2) t - Binf (&1 / &2) t =
      c2_c0_complex (&1 / &2) t * zeta
      ==> c2_zspec Dinf Binf (&1 / &2) t = zeta`,
  MESON_TAC[C2_THM13_RATIO_CRITICAL]);;

let C2_PUBLIC_ZSPEC_RATIO_ON_STRIP_OF_CONTINUATION = prove
 (`!(Dinf:real->real->complex) Binf zeta sigma t.
      c2_continuation_identity Dinf Binf zeta /\
      &0 < sigma
      ==> c2_zspec Dinf Binf sigma t = zeta sigma t`,
  MESON_TAC[C2_ZSPEC_EQ_OF_CONTINUATION]);;

let C2_PUBLIC_ZSPEC_ZERO_IFF_ZETA_ZERO_ON_STRIP_OF_CONTINUATION = prove
 (`!(Dinf:real->real->complex) Binf zeta sigma t.
      c2_continuation_identity Dinf Binf zeta /\
      &0 < sigma
      ==> (c2_zspec Dinf Binf sigma t = Cx(&0) <=>
           zeta sigma t = Cx(&0))`,
  MESON_TAC[C2_CONTINUATION_ZERO_IFF]);;

let C2_PUBLIC_NUMERATOR_NONZERO_IFF_ZETA_NONZERO_ON_STRIP_OF_CONTINUATION = prove
 (`!(Dinf:real->real->complex) Binf zeta sigma t.
      c2_continuation_identity Dinf Binf zeta /\
      &0 < sigma
      ==> (~(Dinf sigma t - Binf sigma t = Cx(&0)) <=>
           ~(zeta sigma t = Cx(&0)))`,
  MESON_TAC[C2_CONTINUATION_NONZERO_IFF_ZETA_NONZERO]);;

let C2_PUBLIC_TRANSVERSAL_SIGMA_PRODUCT_JET_ON_RIGHT_HALFPLANE = prove
 (`!sigma t m (w:num->complex) (cJet:num->complex) (zJet:num->complex) Fjet.
      &0 < sigma /\
      w 0 = Cx(&1) /\
      (!k. k < m ==> zJet k = Cx(&0)) /\
      cJet 0 = c2_c0_complex sigma t /\
      ~(zJet m = Cx(&0)) /\
      Fjet = c2_leibniz_sum m w cJet zJet
      ==> Fjet = c2_c0_complex sigma t * zJet m /\
          ~(Fjet = Cx(&0))`,
  MESON_TAC[C2_THM8_TRANSVERSAL_SIGMA_PRODUCT_JET]);;

let C2_PUBLIC_TRANSVERSAL_SIGMA_PRODUCT_JET_ON_CRITICAL_LINE = prove
 (`!t m (w:num->complex) (cJet:num->complex) (zJet:num->complex) Fjet.
      w 0 = Cx(&1) /\
      (!k. k < m ==> zJet k = Cx(&0)) /\
      cJet 0 = c2_c0_complex (&1 / &2) t /\
      ~(zJet m = Cx(&0)) /\
      Fjet = c2_leibniz_sum m w cJet zJet
      ==> Fjet = c2_c0_complex (&1 / &2) t * zJet m /\
          ~(Fjet = Cx(&0))`,
  MESON_TAC[C2_THM8_TRANSVERSAL_SIGMA_PRODUCT_JET_CRITICAL]);;

let C2_PUBLIC_NUMERATOR_NONZERO_OF_TAYLOR_DOMINANCE = prove
 (`!(Dinf:real->real->complex) Binf sigma t.
      c2_taylor_dominance_at Dinf Binf sigma t
      ==> ~(Dinf sigma t - Binf sigma t = Cx(&0))`,
  MESON_TAC[C2_TAYLOR_DOMINANCE_NUMERATOR_NONZERO]);;

let C2_PUBLIC_ZETA_NONZERO_ON_OFFAXIS_OF_TAYLOR_DOMINANCE = prove
 (`!(Dinf:real->real->complex) Binf zeta.
      c2_continuation_identity Dinf Binf zeta /\
      c2_taylor_dominance_global Dinf Binf
      ==> !sigma t.
            c2_offaxis_strip sigma
            ==> ~(zeta sigma t = Cx(&0))`,
  MESON_TAC[C2_OFFAXIS_ZETA_NONZERO_OF_TAYLOR_DOMINANCE_GLOBAL]);;

let C2_PUBLIC_ZSPEC_NONZERO_ON_OFFAXIS_OF_TAYLOR_DOMINANCE = prove
 (`!(Dinf:real->real->complex) Binf zeta.
      c2_continuation_identity Dinf Binf zeta /\
      c2_taylor_dominance_global Dinf Binf
      ==> !sigma t.
            c2_offaxis_strip sigma
            ==> ~(c2_zspec Dinf Binf sigma t = Cx(&0))`,
  MESON_TAC[C2_FULL_CHAIN_ZSPEC_ENDPOINT_OF_TAYLOR_DOMINANCE]);;

let C2_PUBLIC_ZETA_PARAMETRIC_EXCLUSION_RADIUS = prove
 (`!(Dinf:real->real->complex) Binf zeta A C L.
      c2_continuation_identity Dinf Binf zeta /\
      c2_taylor_dominance_parametric_global Dinf Binf A C L
      ==> !sigma t.
            c2_offaxis_strip sigma
            ==> ~(zeta sigma t = Cx(&0)) /\
                ?mu M2 delta deltaStar.
                  &0 < mu /\
                  &0 < M2 /\
                  &0 < delta /\
                  deltaStar = &2 * mu / M2 /\
                  delta < deltaStar /\
                  &0 < deltaStar /\
                  &2 * mu / (&2 * A + C * L) <= deltaStar`,
  MESON_TAC[C2_FULL_CHAIN_ZETA_PARAMETRIC_EXCLUSION_RADIUS]);;

let C2_PUBLIC_ZSPEC_PARAMETRIC_EXCLUSION_RADIUS = prove
 (`!(Dinf:real->real->complex) Binf zeta A C L.
      c2_continuation_identity Dinf Binf zeta /\
      c2_taylor_dominance_parametric_global Dinf Binf A C L
      ==> !sigma t.
            c2_offaxis_strip sigma
            ==> ~(c2_zspec Dinf Binf sigma t = Cx(&0)) /\
                ?mu M2 delta deltaStar.
                  &0 < mu /\
                  &0 < M2 /\
                  &0 < delta /\
                  deltaStar = &2 * mu / M2 /\
                  delta < deltaStar /\
                  &0 < deltaStar /\
                  &2 * mu / (&2 * A + C * L) <= deltaStar`,
  MESON_TAC[C2_FULL_CHAIN_ZSPEC_PARAMETRIC_EXCLUSION_RADIUS]);;

let C2_PUBLIC_ZETA_HEIGHT_LOGSQ_EXCLUSION_RADIUS = prove
 (`!(Dinf:real->real->complex) Binf zeta A C.
      c2_continuation_identity Dinf Binf zeta /\
      c2_taylor_dominance_height_logsq_global Dinf Binf A C
      ==> !sigma t.
            c2_offaxis_strip sigma
            ==> ~(zeta sigma t = Cx(&0)) /\
                ?mu M2 delta deltaStar.
                  &0 < mu /\
                  &0 < M2 /\
                  &0 < delta /\
                  deltaStar = &2 * mu / M2 /\
                  delta < deltaStar /\
                  &0 < deltaStar /\
                  &2 * mu / c2_logsq_m2_envelope A C sigma t <= deltaStar`,
  MESON_TAC[C2_FULL_CHAIN_ZETA_HEIGHT_LOGSQ_EXCLUSION_RADIUS]);;

let C2_PUBLIC_ZSPEC_HEIGHT_LOGSQ_EXCLUSION_RADIUS = prove
 (`!(Dinf:real->real->complex) Binf zeta A C.
      c2_continuation_identity Dinf Binf zeta /\
      c2_taylor_dominance_height_logsq_global Dinf Binf A C
      ==> !sigma t.
            c2_offaxis_strip sigma
            ==> ~(c2_zspec Dinf Binf sigma t = Cx(&0)) /\
                ?mu M2 delta deltaStar.
                  &0 < mu /\
                  &0 < M2 /\
                  &0 < delta /\
                  deltaStar = &2 * mu / M2 /\
                  delta < deltaStar /\
                  &0 < deltaStar /\
                  &2 * mu / c2_logsq_m2_envelope A C sigma t <= deltaStar`,
  MESON_TAC[C2_FULL_CHAIN_ZSPEC_HEIGHT_LOGSQ_EXCLUSION_RADIUS]);;

let C2_PUBLIC_GLOBAL_ZERO_EXCLUSION_OF_NUMERATOR_TRANSVERSAL_PRODUCT_JET = prove
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
  MESON_TAC[C2_GLOBAL_ZERO_EXCLUSION_OF_NUMERATOR_TRANSVERSAL_PRODUCT_JET]);;