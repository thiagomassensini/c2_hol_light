(* ------------------------------------------------------------------------- *)
(* C2 route K: meromorphic continuation bridge for the Thm 17 identity.      *)
(* ------------------------------------------------------------------------- *)

prioritize_complex();;

let c2_open_right_halfplane = new_definition
 `c2_open_right_halfplane = {z:complex | &0 < Re z}`;;

let c2_punctured_open_right_halfplane = new_definition
 `c2_punctured_open_right_halfplane =
    {z:complex | &0 < Re z /\ ~(z = Cx(&1))}`;;

let c2_right_halfplane_gt_one = new_definition
 `c2_right_halfplane_gt_one = {z:complex | &1 < Re z}`;;

let c2_continued_numerator = new_definition
 `(c2_continued_numerator:
    (real->real->complex)->(real->real->complex)->complex->complex)
    Dinf Binf z = Dinf (Re z) (Im z) - Binf (Re z) (Im z)`;;

let c2_continued_product = new_definition
 `(c2_continued_product:
    (real->real->complex)->complex->complex)
    zeta z = c2_c0_complex (Re z) (Im z) * zeta (Re z) (Im z)`;;

let c2_pole_cleared_numerator = new_definition
 `(c2_pole_cleared_numerator:
    (real->real->complex)->(real->real->complex)->complex->complex)
    Dinf Binf z =
    (z - Cx(&1)) * c2_continued_numerator Dinf Binf z`;;

let c2_pole_cleared_product = new_definition
 `(c2_pole_cleared_product:
    (real->real->complex)->complex->complex)
    zeta z =
    (z - Cx(&1)) * c2_continued_product zeta z`;;

let c2_seed_identity_on_gt_one = new_definition
 `(c2_seed_identity_on_gt_one:
    (real->real->complex)->(real->real->complex)->
    (real->real->complex)->bool) Dinf Binf zeta <=>
    !z. z IN c2_right_halfplane_gt_one ==>
        c2_continued_numerator Dinf Binf z = c2_continued_product zeta z`;;

let c2_pole_cleared_continuation_data = new_definition
 `(c2_pole_cleared_continuation_data:
    (real->real->complex)->(real->real->complex)->
    (real->real->complex)->bool) Dinf Binf zeta <=>
    (c2_pole_cleared_numerator Dinf Binf) analytic_on
      c2_open_right_halfplane /\
    (c2_pole_cleared_product zeta) analytic_on c2_open_right_halfplane /\
    c2_seed_identity_on_gt_one Dinf Binf zeta`;;

let c2_thm17_punctured_halfplane_eq = new_definition
 `(c2_thm17_punctured_halfplane_eq:
    (real->real->complex)->(real->real->complex)->bool) f g <=>
    !sigma t.
      &0 < sigma /\ ~(sigma = &1 /\ t = &0) ==> f sigma t = g sigma t`;;

let c2_continuation_identity_punctured = new_definition
 `(c2_continuation_identity_punctured:
    (real->real->complex)->(real->real->complex)->
    (real->real->complex)->bool) Dinf Binf zeta <=>
    c2_thm17_punctured_halfplane_eq
      (\sigma t. Dinf sigma t - Binf sigma t)
      (\sigma t. c2_c0_complex sigma t * zeta sigma t)`;;

let C2_OPEN_RIGHT_HALFPLANE_OPEN = prove
 (`open c2_open_right_halfplane`,
  REWRITE_TAC[c2_open_right_halfplane; OPEN_HALFSPACE_RE_GT]);;

let C2_PUNCTURED_OPEN_RIGHT_HALFPLANE_OPEN = prove
 (`open c2_punctured_open_right_halfplane`,
  REWRITE_TAC[c2_punctured_open_right_halfplane; OPEN_DELETE;
              C2_OPEN_RIGHT_HALFPLANE_OPEN; CLOSED_SING]);;

let C2_OPEN_RIGHT_HALFPLANE_CONNECTED = prove
 (`connected c2_open_right_halfplane`,
  MATCH_MP_TAC CONVEX_CONNECTED THEN
  REWRITE_TAC[c2_open_right_halfplane; CONVEX_HALFSPACE_RE_GT]);;

let C2_RIGHT_HALFPLANE_GT_ONE_OPEN = prove
 (`open c2_right_halfplane_gt_one`,
  REWRITE_TAC[c2_right_halfplane_gt_one; OPEN_HALFSPACE_RE_GT]);;

let C2_RIGHT_HALFPLANE_GT_ONE_SUBSET_OPEN_RIGHT_HALFPLANE = prove
 (`c2_right_halfplane_gt_one SUBSET c2_open_right_halfplane`,
  REWRITE_TAC[c2_right_halfplane_gt_one; c2_open_right_halfplane; SUBSET;
              IN_ELIM_THM] THEN
  REAL_ARITH_TAC);;

let C2_RIGHT_HALFPLANE_GT_ONE_LIMPT_2 = prove
 (`Cx(&2) limit_point_of c2_right_halfplane_gt_one`,
  MATCH_MP_TAC LIMPT_OF_OPEN THEN
  REWRITE_TAC[C2_RIGHT_HALFPLANE_GT_ONE_OPEN;
              c2_right_halfplane_gt_one; IN_ELIM_THM; RE_CX] THEN
  REAL_ARITH_TAC);;

let C2_CONTINUED_NUMERATOR_AT_COMPLEX = prove
 (`!(Dinf:real->real->complex) Binf sigma t.
      c2_continued_numerator Dinf Binf (complex(sigma,t)) =
      Dinf sigma t - Binf sigma t`,
  REWRITE_TAC[c2_continued_numerator; RE; IM]);;

let C2_CONTINUED_PRODUCT_AT_COMPLEX = prove
 (`!(zeta:real->real->complex) sigma t.
      c2_continued_product zeta (complex(sigma,t)) =
      c2_c0_complex sigma t * zeta sigma t`,
  REWRITE_TAC[c2_continued_product; RE; IM]);;

let C2_SEED_IDENTITY_ON_GT_ONE_OF_COORDINATES = prove
 (`!(Dinf:real->real->complex) Binf zeta.
      (!sigma t.
          &1 < sigma ==>
          Dinf sigma t - Binf sigma t =
          c2_c0_complex sigma t * zeta sigma t)
      ==> c2_seed_identity_on_gt_one Dinf Binf zeta`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c2_seed_identity_on_gt_one; c2_right_halfplane_gt_one;
              IN_ELIM_THM; c2_continued_numerator; c2_continued_product] THEN
  MESON_TAC[]);;

let C2_PUNCTURED_CONTINUATION_IDENTITY_OFFAXIS = prove
 (`!(Dinf:real->real->complex) Binf zeta sigma t.
      c2_continuation_identity_punctured Dinf Binf zeta /\
      &0 < sigma /\ ~(sigma = &1 /\ t = &0)
      ==> Dinf sigma t - Binf sigma t =
          c2_c0_complex sigma t * zeta sigma t`,
  REWRITE_TAC[c2_continuation_identity_punctured;
              c2_thm17_punctured_halfplane_eq] THEN
  MESON_TAC[]);;

let C2_PUNCTURED_CONTINUATION_IDENTITY_ON_OFFAXIS_STRIP = prove
 (`!(Dinf:real->real->complex) Binf zeta sigma t.
      c2_continuation_identity_punctured Dinf Binf zeta /\
      &0 < sigma /\ sigma < &1
      ==> Dinf sigma t - Binf sigma t =
          c2_c0_complex sigma t * zeta sigma t`,
  MESON_TAC[C2_PUNCTURED_CONTINUATION_IDENTITY_OFFAXIS; REAL_ARITH
   `&0 < sigma /\ sigma < &1 ==> ~(sigma = &1 /\ t = &0)`]);;

let C2_CONTINUATION_IDENTITY_PUNCTURED_OF_POLE_CLEARED_DATA = prove
 (`!(Dinf:real->real->complex) Binf zeta.
      c2_pole_cleared_continuation_data Dinf Binf zeta
      ==> c2_continuation_identity_punctured Dinf Binf zeta`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[c2_pole_cleared_continuation_data;
              c2_continuation_identity_punctured;
              c2_thm17_punctured_halfplane_eq] THEN
  DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  ABBREV_TAC
   `h:complex->complex =
      \z. c2_pole_cleared_numerator Dinf Binf z - c2_pole_cleared_product zeta z` THEN
  SUBGOAL_THEN `h holomorphic_on c2_open_right_halfplane` ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN MATCH_MP_TAC ANALYTIC_IMP_HOLOMORPHIC THEN
    MATCH_MP_TAC ANALYTIC_ON_SUB THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN c2_right_halfplane_gt_one ==> h w = Cx(&0)` ASSUME_TAC THENL
   [X_GEN_TAC `w:complex` THEN DISCH_TAC THEN EXPAND_TAC "h" THEN
    SUBGOAL_THEN
     `c2_continued_numerator Dinf Binf w = c2_continued_product zeta w`
    SUBST1_TAC THENL
     [ASM_MESON_TAC[c2_seed_identity_on_gt_one];
      REWRITE_TAC[c2_pole_cleared_numerator; c2_pole_cleared_product;
                  COMPLEX_SUB_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. w IN c2_open_right_halfplane ==> h w = Cx(&0)` ASSUME_TAC THENL
   [MATCH_MP_TAC
     (SPECL [`h:complex->complex`; `c2_open_right_halfplane`;
             `c2_right_halfplane_gt_one`; `Cx(&2)`]
            ANALYTIC_CONTINUATION) THEN
    ASM_REWRITE_TAC[C2_OPEN_RIGHT_HALFPLANE_OPEN;
                    C2_OPEN_RIGHT_HALFPLANE_CONNECTED;
                    C2_RIGHT_HALFPLANE_GT_ONE_SUBSET_OPEN_RIGHT_HALFPLANE;
                    C2_RIGHT_HALFPLANE_GT_ONE_LIMPT_2] THEN
    REWRITE_TAC[c2_open_right_halfplane; IN_ELIM_THM; RE_CX] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `sigma:real` THEN
  X_GEN_TAC `t:real` THEN
  STRIP_TAC THEN
  MP_TAC(SPEC `complex(sigma,t)` (ASSUME
   `!w. w IN c2_open_right_halfplane ==> h w = Cx(&0)`)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[c2_open_right_halfplane; IN_ELIM_THM; RE] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  POP_ASSUM MP_TAC THEN
  EXPAND_TAC "h" THEN
  REWRITE_TAC[c2_pole_cleared_numerator; c2_pole_cleared_product;
              C2_CONTINUED_NUMERATOR_AT_COMPLEX;
              C2_CONTINUED_PRODUCT_AT_COMPLEX] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `(complex(sigma,t) - Cx(&1)) *
    ((Dinf sigma t - Binf sigma t) - c2_c0_complex sigma t * zeta sigma t) =
    Cx(&0)`
  ASSUME_TAC THENL
   [POP_ASSUM MP_TAC THEN CONV_TAC COMPLEX_RING;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(complex(sigma,t):complex = Cx(&1))` ASSUME_TAC THENL
   [REWRITE_TAC[COMPLEX_EQ; RE; IM; RE_CX; IM_CX] THEN ASM_REAL_ARITH_TAC;
    SUBGOAL_THEN
     `~(complex(sigma,t):complex - Cx(&1) = Cx(&0))` ASSUME_TAC THENL
     [ASM_MESON_TAC[COMPLEX_SUB_0];
      MP_TAC(ASSUME
       `(complex(sigma,t) - Cx(&1)) *
        ((Dinf sigma t - Binf sigma t) - c2_c0_complex sigma t * zeta sigma t) =
        Cx(&0)`) THEN
      ASM_SIMP_TAC[COMPLEX_ENTIRE] THEN
      REWRITE_TAC[COMPLEX_SUB_0]]]);;

let C2_CONTINUATION_IDENTITY_PUNCTURED_OF_POLE_CLEARED_ANALYTIC = prove
 (`!(Dinf:real->real->complex) Binf zeta.
      (c2_pole_cleared_numerator Dinf Binf) analytic_on c2_open_right_halfplane /\
      (c2_pole_cleared_product zeta) analytic_on c2_open_right_halfplane /\
      (!sigma t.
          &1 < sigma ==>
          Dinf sigma t - Binf sigma t =
          c2_c0_complex sigma t * zeta sigma t)
      ==> c2_continuation_identity_punctured Dinf Binf zeta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C2_CONTINUATION_IDENTITY_PUNCTURED_OF_POLE_CLEARED_DATA THEN
  REWRITE_TAC[c2_pole_cleared_continuation_data] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C2_SEED_IDENTITY_ON_GT_ONE_OF_COORDINATES THEN
  ASM_REWRITE_TAC[]);;

let C2_CONTINUATION_IDENTITY_OF_POLE_CLEARED_DATA = prove
 (`!(Dinf:real->real->complex) Binf zeta.
      c2_pole_cleared_continuation_data Dinf Binf zeta /\
      Dinf (&1) (&0) - Binf (&1) (&0) =
      c2_c0_complex (&1) (&0) * zeta (&1) (&0)
      ==> c2_continuation_identity Dinf Binf zeta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`Dinf:real->real->complex`; `Binf:real->real->complex`;
                `zeta:real->real->complex`]
               C2_CONTINUATION_IDENTITY_PUNCTURED_OF_POLE_CLEARED_DATA) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[c2_continuation_identity_punctured;
              c2_continuation_identity;
              c2_thm17_punctured_halfplane_eq;
              c2_thm17_halfplane_eq] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN
   `!sigma t.
      &0 < sigma /\ ~(sigma = &1 /\ t = &0)
      ==> Dinf sigma t - Binf sigma t =
          c2_c0_complex sigma t * zeta sigma t`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[];
    X_GEN_TAC `sigma:real` THEN
    X_GEN_TAC `t:real` THEN
    DISCH_TAC THEN
    ASM_CASES_TAC `sigma = &1 /\ t = &0` THEN
    ASM_MESON_TAC[]]);;

let C2_CONTINUATION_IDENTITY_OF_POLE_CLEARED_ANALYTIC = prove
 (`!(Dinf:real->real->complex) Binf zeta.
      (c2_pole_cleared_numerator Dinf Binf) analytic_on c2_open_right_halfplane /\
      (c2_pole_cleared_product zeta) analytic_on c2_open_right_halfplane /\
      (!sigma t.
          &1 < sigma ==>
          Dinf sigma t - Binf sigma t =
          c2_c0_complex sigma t * zeta sigma t) /\
      Dinf (&1) (&0) - Binf (&1) (&0) =
      c2_c0_complex (&1) (&0) * zeta (&1) (&0)
      ==> c2_continuation_identity Dinf Binf zeta`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC C2_CONTINUATION_IDENTITY_OF_POLE_CLEARED_DATA THEN
  ASM_REWRITE_TAC[c2_pole_cleared_continuation_data] THEN
  MATCH_MP_TAC C2_SEED_IDENTITY_ON_GT_ONE_OF_COORDINATES THEN
  ASM_REWRITE_TAC[]);;