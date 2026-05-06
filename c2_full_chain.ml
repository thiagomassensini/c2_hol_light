(* ------------------------------------------------------------------------- *)
(* C2 route K: full-chain Taylor endpoint interface, HOL Light port.         *)
(*                                                                           *)
(* Lean references:                                                          *)
(*   formal/lean_c2/LeanC2/TransversalAnalytic.lean                          *)
(*   formal/lean_c2/LeanC2/FullChain.lean                                    *)
(*                                                                           *)
(* This layer packages the endpoint-facing consequences of a pointwise       *)
(* Taylor-dominance witness for the continued numerator Dinf - Binf.         *)
(* The analytic Taylor witness itself remains an explicit hypothesis; once   *)
(* supplied, HOL proves numerator nonvanishing, radius extraction, and the   *)
(* transfer to zeta and Z_spec through the already formalized continuation   *)
(* identity interface.                                                       *)
(* ------------------------------------------------------------------------- *)

prioritize_complex();;

let c2_offaxis_strip = new_definition
 `c2_offaxis_strip sigma <=>
    &0 < sigma /\ sigma < &1 /\ ~(sigma = &1 / &2)`;;

let c2_taylor_gap = new_definition
 `c2_taylor_gap mu M2 R delta =
    delta * mu - (delta pow 2 / &2) * M2 - R`;;

let c2_taylor_dominance_at = new_definition
 `(c2_taylor_dominance_at:
    (real->real->complex)->(real->real->complex)->real->real->bool)
    Dinf Binf sigma t <=>
    ?mu M2 R delta.
      &0 < mu /\
      &0 < M2 /\
      &0 < delta /\
      delta < &2 * mu / M2 /\
      &0 <= R /\
      &0 < c2_taylor_gap mu M2 R delta /\
      c2_taylor_gap mu M2 R delta <= norm(Dinf sigma t - Binf sigma t)`;;

let c2_taylor_dominance_global = new_definition
 `(c2_taylor_dominance_global:
    (real->real->complex)->(real->real->complex)->bool) Dinf Binf <=>
    !sigma t.
      c2_offaxis_strip sigma
      ==> c2_taylor_dominance_at Dinf Binf sigma t`;;

let c2_taylor_dominance_envelope_at = new_definition
 `(c2_taylor_dominance_envelope_at:
    (real->real->complex)->(real->real->complex)->
    (real->real->real)->real->real->bool)
    Dinf Binf M2Envelope sigma t <=>
    ?mu M2 R delta.
      &0 < mu /\
      &0 < M2 /\
      &0 < delta /\
      delta < &2 * mu / M2 /\
      &0 <= R /\
      &0 < c2_taylor_gap mu M2 R delta /\
      c2_taylor_gap mu M2 R delta <= norm(Dinf sigma t - Binf sigma t) /\
      M2 <= M2Envelope sigma t /\
      &2 * mu / M2Envelope sigma t <= &2 * mu / M2`;;

let c2_taylor_dominance_envelope_global = new_definition
 `(c2_taylor_dominance_envelope_global:
    (real->real->complex)->(real->real->complex)->
    (real->real->real)->bool) Dinf Binf M2Envelope <=>
    !sigma t.
      c2_offaxis_strip sigma
      ==> c2_taylor_dominance_envelope_at
            Dinf Binf M2Envelope sigma t`;;

let c2_parametric_m2_envelope = new_definition
 `(c2_parametric_m2_envelope:real->real->real->real->real->real)
    A C L sigma t = &2 * A + C * L`;;

let c2_taylor_dominance_parametric_global = new_definition
 `(c2_taylor_dominance_parametric_global:
    (real->real->complex)->(real->real->complex)->
    real->real->real->bool) Dinf Binf A C L <=>
    c2_taylor_dominance_envelope_global
      Dinf Binf (c2_parametric_m2_envelope A C L)`;;

let c2_logsq_m2_envelope = new_definition
 `(c2_logsq_m2_envelope:real->real->real->real->real) A C sigma t =
    &2 * A + C * (ln(abs t)) pow 2`;;

let c2_taylor_dominance_height_logsq_global = new_definition
 `(c2_taylor_dominance_height_logsq_global:
    (real->real->complex)->(real->real->complex)->
    real->real->bool) Dinf Binf A C <=>
    c2_taylor_dominance_envelope_global
      Dinf Binf (c2_logsq_m2_envelope A C)`;;

let C2_TAYLOR_DOMINANCE_AT_OF_ENVELOPE = prove
 (`!(Dinf:real->real->complex) Binf M2Envelope sigma t.
      c2_taylor_dominance_envelope_at Dinf Binf M2Envelope sigma t
      ==> c2_taylor_dominance_at Dinf Binf sigma t`,
  REWRITE_TAC[c2_taylor_dominance_envelope_at;
              c2_taylor_dominance_at] THEN
  MESON_TAC[]);;

let C2_TAYLOR_DOMINANCE_GLOBAL_OF_ENVELOPE = prove
 (`!(Dinf:real->real->complex) Binf M2Envelope.
      c2_taylor_dominance_envelope_global Dinf Binf M2Envelope
      ==> c2_taylor_dominance_global Dinf Binf`,
  REWRITE_TAC[c2_taylor_dominance_envelope_global;
              c2_taylor_dominance_global] THEN
  MESON_TAC[C2_TAYLOR_DOMINANCE_AT_OF_ENVELOPE]);;

let C2_TAYLOR_DOMINANCE_NUMERATOR_NORM_POS = prove
  (`!(Dinf:real->real->complex) Binf sigma t.
      c2_taylor_dominance_at Dinf Binf sigma t
      ==> &0 < norm(Dinf sigma t - Binf sigma t)`,
  REWRITE_TAC[c2_taylor_dominance_at] THEN
  MESON_TAC[REAL_LTE_TRANS]);;

let C2_TAYLOR_DOMINANCE_NUMERATOR_NONZERO = prove
 (`!(Dinf:real->real->complex) Binf sigma t.
      c2_taylor_dominance_at Dinf Binf sigma t
      ==> ~(Dinf sigma t - Binf sigma t = Cx(&0))`,
  MESON_TAC[C2_TAYLOR_DOMINANCE_NUMERATOR_NORM_POS;
            COMPLEX_NORM_NZ]);;

let C2_TAYLOR_EXCLUSION_RADIUS_DATA_AT = prove
 (`!(Dinf:real->real->complex) Binf sigma t.
      c2_taylor_dominance_at Dinf Binf sigma t
      ==> ?mu M2 delta deltaStar.
            &0 < mu /\
            &0 < M2 /\
            &0 < delta /\
            deltaStar = &2 * mu / M2 /\
            delta < deltaStar /\
            &0 < deltaStar`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c2_taylor_dominance_at] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `M2:real` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `mu:real` THEN
  EXISTS_TAC `M2:real` THEN
  EXISTS_TAC `delta:real` THEN
  EXISTS_TAC `&2 * mu / M2` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH]);;

let C2_TAYLOR_ENVELOPE_EXCLUSION_RADIUS_DATA_AT = prove
 (`!(Dinf:real->real->complex) Binf M2Envelope sigma t.
      c2_taylor_dominance_envelope_at Dinf Binf M2Envelope sigma t
      ==> ?mu M2 delta deltaStar.
            &0 < mu /\
            &0 < M2 /\
            &0 < delta /\
            deltaStar = &2 * mu / M2 /\
            delta < deltaStar /\
            &0 < deltaStar /\
            &2 * mu / M2Envelope sigma t <= deltaStar`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c2_taylor_dominance_envelope_at] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `M2:real` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `mu:real` THEN
  EXISTS_TAC `M2:real` THEN
  EXISTS_TAC `delta:real` THEN
  EXISTS_TAC `&2 * mu / M2` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MUL; REAL_OF_NUM_LT; ARITH]);;

let C2_OFFAXIS_TAYLOR_EXCLUSION_RADIUS_DATA_GLOBAL = prove
 (`!(Dinf:real->real->complex) Binf.
      c2_taylor_dominance_global Dinf Binf
      ==> !sigma (t:real).
            c2_offaxis_strip sigma
            ==> ?mu M2 delta deltaStar.
                  &0 < mu /\
                  &0 < M2 /\
                  &0 < delta /\
                  deltaStar = &2 * mu / M2 /\
                  delta < deltaStar /\
                  &0 < deltaStar`,
  REWRITE_TAC[c2_taylor_dominance_global] THEN
  MESON_TAC[C2_TAYLOR_EXCLUSION_RADIUS_DATA_AT]);;

let C2_OFFAXIS_TAYLOR_ENVELOPE_EXCLUSION_RADIUS_DATA_GLOBAL = prove
 (`!(Dinf:real->real->complex) Binf M2Envelope.
      c2_taylor_dominance_envelope_global Dinf Binf M2Envelope
      ==> !sigma t.
            c2_offaxis_strip sigma
            ==> ?mu M2 delta deltaStar.
                  &0 < mu /\
                  &0 < M2 /\
                  &0 < delta /\
                  deltaStar = &2 * mu / M2 /\
                  delta < deltaStar /\
                  &0 < deltaStar /\
                  &2 * mu / M2Envelope sigma t <= deltaStar`,
  REWRITE_TAC[c2_taylor_dominance_envelope_global] THEN
  MESON_TAC[C2_TAYLOR_ENVELOPE_EXCLUSION_RADIUS_DATA_AT]);;

let C2_OFFAXIS_NUMERATOR_NORM_POS_OF_TAYLOR_DOMINANCE_GLOBAL = prove
 (`!(Dinf:real->real->complex) Binf.
      c2_taylor_dominance_global Dinf Binf
      ==> !sigma t.
            c2_offaxis_strip sigma
            ==> &0 < norm(Dinf sigma t - Binf sigma t)`,
  REWRITE_TAC[c2_taylor_dominance_global] THEN
  MESON_TAC[C2_TAYLOR_DOMINANCE_NUMERATOR_NORM_POS]);;

let C2_OFFAXIS_NUMERATOR_NONZERO_OF_TAYLOR_DOMINANCE_GLOBAL = prove
 (`!(Dinf:real->real->complex) Binf.
      c2_taylor_dominance_global Dinf Binf
      ==> !sigma t.
            c2_offaxis_strip sigma
            ==> ~(Dinf sigma t - Binf sigma t = Cx(&0))`,
  REWRITE_TAC[c2_taylor_dominance_global] THEN
  MESON_TAC[C2_TAYLOR_DOMINANCE_NUMERATOR_NONZERO]);;

let C2_OFFAXIS_ZETA_NONZERO_OF_TAYLOR_DOMINANCE_GLOBAL = prove
  (`!(Dinf:real->real->complex) Binf zeta.
      c2_continuation_identity Dinf Binf zeta /\
      c2_taylor_dominance_global Dinf Binf
      ==> !sigma t.
            c2_offaxis_strip sigma
            ==> ~(zeta sigma t = Cx(&0))`,
  MESON_TAC[c2_offaxis_strip;
            C2_OFFAXIS_NUMERATOR_NONZERO_OF_TAYLOR_DOMINANCE_GLOBAL;
            C2_CONTINUATION_NONZERO_IFF_ZETA_NONZERO]);;

let C2_OFFAXIS_ZETA_NORM_POS_OF_TAYLOR_DOMINANCE_GLOBAL = prove
 (`!(Dinf:real->real->complex) Binf zeta.
      c2_continuation_identity Dinf Binf zeta /\
      c2_taylor_dominance_global Dinf Binf
      ==> !sigma t.
            c2_offaxis_strip sigma
            ==> &0 < norm(zeta sigma t)`,
  MESON_TAC[C2_OFFAXIS_ZETA_NONZERO_OF_TAYLOR_DOMINANCE_GLOBAL;
            COMPLEX_NORM_NZ]);;

let C2_FULL_CHAIN_ZSPEC_ENDPOINT_OF_TAYLOR_DOMINANCE = prove
  (`!(Dinf:real->real->complex) Binf zeta.
      c2_continuation_identity Dinf Binf zeta /\
      c2_taylor_dominance_global Dinf Binf
      ==> !sigma t.
            c2_offaxis_strip sigma
            ==> ~(c2_zspec Dinf Binf sigma t = Cx(&0))`,
  MESON_TAC[c2_offaxis_strip;
            C2_OFFAXIS_ZETA_NONZERO_OF_TAYLOR_DOMINANCE_GLOBAL;
            C2_ZSPEC_EQ_OF_CONTINUATION]);;

let C2_FULL_CHAIN_ZSPEC_NORM_POS_OF_TAYLOR_DOMINANCE = prove
 (`!(Dinf:real->real->complex) Binf zeta.
      c2_continuation_identity Dinf Binf zeta /\
      c2_taylor_dominance_global Dinf Binf
      ==> !sigma t.
            c2_offaxis_strip sigma
            ==> &0 < norm(c2_zspec Dinf Binf sigma t)`,
  MESON_TAC[C2_FULL_CHAIN_ZSPEC_ENDPOINT_OF_TAYLOR_DOMINANCE;
            COMPLEX_NORM_NZ]);;

let C2_FULL_CHAIN_ZETA_ENVELOPE_EXCLUSION_RADIUS =
 prove
 (`!(Dinf:real->real->complex) Binf zeta M2Envelope.
      c2_continuation_identity Dinf Binf zeta /\
      c2_taylor_dominance_envelope_global Dinf Binf M2Envelope
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
	                  &2 * mu / M2Envelope sigma t <= deltaStar`,
  MESON_TAC[C2_TAYLOR_DOMINANCE_GLOBAL_OF_ENVELOPE;
            C2_OFFAXIS_ZETA_NONZERO_OF_TAYLOR_DOMINANCE_GLOBAL;
            C2_OFFAXIS_TAYLOR_ENVELOPE_EXCLUSION_RADIUS_DATA_GLOBAL]);;

let C2_FULL_CHAIN_ZSPEC_ENVELOPE_EXCLUSION_RADIUS =
 prove
 (`!(Dinf:real->real->complex) Binf zeta M2Envelope.
      c2_continuation_identity Dinf Binf zeta /\
      c2_taylor_dominance_envelope_global Dinf Binf M2Envelope
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
	                  &2 * mu / M2Envelope sigma t <= deltaStar`,
  MESON_TAC[C2_TAYLOR_DOMINANCE_GLOBAL_OF_ENVELOPE;
            C2_FULL_CHAIN_ZSPEC_ENDPOINT_OF_TAYLOR_DOMINANCE;
            C2_OFFAXIS_TAYLOR_ENVELOPE_EXCLUSION_RADIUS_DATA_GLOBAL]);;

let C2_FULL_CHAIN_ZETA_PARAMETRIC_EXCLUSION_RADIUS = prove
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
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c2_taylor_dominance_parametric_global] THEN
  STRIP_TAC THEN
  X_GEN_TAC `sigma:real` THEN
  X_GEN_TAC `t:real` THEN
  DISCH_TAC THEN
  MP_TAC
    (SPECL [`Dinf:real->real->complex`; `Binf:real->real->complex`;
            `zeta:real->real->complex`;
            `c2_parametric_m2_envelope A C L`]
           C2_FULL_CHAIN_ZETA_ENVELOPE_EXCLUSION_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`sigma:real`; `t:real`]) THEN
  ASM_REWRITE_TAC[c2_parametric_m2_envelope]);;

let C2_FULL_CHAIN_ZSPEC_PARAMETRIC_EXCLUSION_RADIUS = prove
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
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c2_taylor_dominance_parametric_global] THEN
  STRIP_TAC THEN
  X_GEN_TAC `sigma:real` THEN
  X_GEN_TAC `t:real` THEN
  DISCH_TAC THEN
  MP_TAC
    (SPECL [`Dinf:real->real->complex`; `Binf:real->real->complex`;
            `zeta:real->real->complex`;
            `c2_parametric_m2_envelope A C L`]
           C2_FULL_CHAIN_ZSPEC_ENVELOPE_EXCLUSION_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`sigma:real`; `t:real`]) THEN
  ASM_REWRITE_TAC[c2_parametric_m2_envelope]);;

let C2_FULL_CHAIN_ZETA_HEIGHT_LOGSQ_EXCLUSION_RADIUS = prove
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
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c2_taylor_dominance_height_logsq_global] THEN
  STRIP_TAC THEN
  X_GEN_TAC `sigma:real` THEN
  X_GEN_TAC `t:real` THEN
  DISCH_TAC THEN
  MP_TAC
    (SPECL [`Dinf:real->real->complex`; `Binf:real->real->complex`;
            `zeta:real->real->complex`; `c2_logsq_m2_envelope A C`]
           C2_FULL_CHAIN_ZETA_ENVELOPE_EXCLUSION_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`sigma:real`; `t:real`]) THEN
  ASM_REWRITE_TAC[]);;

let C2_FULL_CHAIN_ZSPEC_HEIGHT_LOGSQ_EXCLUSION_RADIUS = prove
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
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c2_taylor_dominance_height_logsq_global] THEN
  STRIP_TAC THEN
  X_GEN_TAC `sigma:real` THEN
  X_GEN_TAC `t:real` THEN
  DISCH_TAC THEN
  MP_TAC
    (SPECL [`Dinf:real->real->complex`; `Binf:real->real->complex`;
            `zeta:real->real->complex`; `c2_logsq_m2_envelope A C`]
           C2_FULL_CHAIN_ZSPEC_ENVELOPE_EXCLUSION_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`sigma:real`; `t:real`]) THEN
  ASM_REWRITE_TAC[]);;
