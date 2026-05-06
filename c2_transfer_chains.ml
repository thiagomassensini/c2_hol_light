(* ------------------------------------------------------------------------- *)
(* C2 route K: transfer chains from lower bounds to Z_X estimates.           *)
(*                                                                           *)
(* Lean reference:                                                           *)
(*   formal/lean_c2/LeanC2/Transfer.lean                                      *)
(*                                                                           *)
(* This layer keeps the analytic lower bound for c0 as an explicit           *)
(* hypothesis/profile.  The HOL statements below prove that once such a      *)
(* lower bound is available, the finite/canonical cutoff residual transfers  *)
(* to the exact Z_X map with the stated uniform error bound.                 *)
(* ------------------------------------------------------------------------- *)

prioritize_complex();;

let C2_CHAIN_THM14_TO_THM10_OFFAXIS = prove
 (`!zeta R c0 L B.
      &0 < L /\ L <= norm(c0) /\ norm(R) <= B * L
      ==> norm(c2_zx zeta R c0 - zeta) <= B`,
  MESON_TAC[C2_ZX_TRANSFER_BOUND_FROM_LOWER]);;

let C2_CHAIN_CUTOFF_TO_THM10_OFFAXIS = prove
 (`!zeta c0 X C theta L B.
      &0 < X /\ norm(theta) <= &1 /\
      &0 < L /\ L <= norm(c0) /\ abs(C) <= B * L * X
      ==> norm(c2_zx zeta (c2_finite_residual X C theta) c0 - zeta) <= B`,
  MESON_TAC[C2_ZX_TRANSFER_FINITE_BOUND]);;

let C2_CHAIN_CUTOFF_TO_THM10_OFFAXIS_CANONICAL = prove
 (`!zeta c0 X C L B.
      &0 < X /\ &0 < L /\ L <= norm(c0) /\ abs(C) <= B * L * X
      ==> norm(c2_zx zeta (c2_finite_residual_canonical X C) c0 - zeta)
          <= B`,
  MESON_TAC[C2_ZX_TRANSFER_FINITE_CANONICAL_BOUND]);;

let C2_CHAIN_CUTOFF_TO_THM10_CRITICAL_CANONICAL = prove
 (`!zeta c0 X C Lcrit B.
      &0 < X /\ &0 < Lcrit /\ Lcrit <= norm(c0) /\
      abs(C) <= B * Lcrit * X
      ==> norm(c2_zx zeta (c2_finite_residual_canonical X C) c0 - zeta)
          <= B`,
  MESON_TAC[C2_ZX_TRANSFER_FINITE_CANONICAL_BOUND]);;

let C2_THM14_PROFILE_LOWER_BOUND_ABSTRACT = prove
 (`!(c0st:real->real->complex) (Lprof:real->real) sigma t.
      &0 < sigma /\
      (!u v. &0 < u ==> Lprof u <= norm(c0st u v))
      ==> Lprof sigma <= norm(c0st sigma t)`,
  MESON_TAC[]);;

let C2_CHAIN_CUTOFF_TO_THM10_SIGMA_OFFAXIS = prove
 (`!(c0st:real->real->complex) (Lprof:real->real) zeta X C theta B sigma t.
      &0 < sigma /\ &0 < X /\ norm(theta) <= &1 /\
      &0 < Lprof sigma /\ Lprof sigma <= norm(c0st sigma t) /\
      abs(C) <= B * Lprof sigma * X
      ==> norm(c2_zx zeta (c2_finite_residual X C theta)
               (c0st sigma t) - zeta) <= B`,
  MESON_TAC[C2_ZX_TRANSFER_FINITE_BOUND]);;

let C2_CHAIN_CUTOFF_TO_THM10_SIGMA_OFFAXIS_CANONICAL = prove
 (`!(c0st:real->real->complex) (Lprof:real->real) zeta X C B sigma t.
      &0 < sigma /\ &0 < X /\
      &0 < Lprof sigma /\ Lprof sigma <= norm(c0st sigma t) /\
      abs(C) <= B * Lprof sigma * X
      ==> norm(c2_zx zeta (c2_finite_residual_canonical X C)
               (c0st sigma t) - zeta) <= B`,
  MESON_TAC[C2_ZX_TRANSFER_FINITE_CANONICAL_BOUND]);;

let C2_GLOBAL_PROFILE_LOWER_BOUND = prove
 (`!(c0st:real->real->complex) (Lprof:real->real).
      (!sigma t. &0 < sigma
                 ==> &0 < Lprof sigma /\
                     Lprof sigma <= norm(c0st sigma t))
      ==> !sigma t. &0 < sigma
                    ==> &0 < Lprof sigma /\
                        Lprof sigma <= norm(c0st sigma t)`,
  MESON_TAC[]);;

let C2_GLOBAL_CUTOFF_TO_THM10_OFFAXIS_CANONICAL = prove
 (`!(c0st:real->real->complex) (Lprof:real->real) zeta X C B.
      &0 < X /\
      (!sigma t. &0 < sigma
                 ==> &0 < Lprof sigma /\
                     Lprof sigma <= norm(c0st sigma t))
      ==> !sigma t.
          &0 < sigma /\ abs(C) <= B * Lprof sigma * X
          ==> norm(c2_zx zeta (c2_finite_residual_canonical X C)
                   (c0st sigma t) - zeta) <= B`,
  MESON_TAC[C2_ZX_TRANSFER_FINITE_CANONICAL_BOUND]);;

let C2_GLOBAL_CUTOFF_TO_THM10_OFFAXIS = prove
 (`!(c0st:real->real->complex) (Lprof:real->real) zeta X C theta B.
      &0 < X /\ norm(theta) <= &1 /\
      (!sigma t. &0 < sigma
                 ==> &0 < Lprof sigma /\
                     Lprof sigma <= norm(c0st sigma t))
      ==> !sigma t.
          &0 < sigma /\ abs(C) <= B * Lprof sigma * X
          ==> norm(c2_zx zeta (c2_finite_residual X C theta)
                   (c0st sigma t) - zeta) <= B`,
  MESON_TAC[C2_ZX_TRANSFER_FINITE_BOUND]);;

let C2_THM14_UNIFORM_BAND_PROFILE_POINT = prove
 (`!(Lprof:real->real) L0 sigma0 sigma1 sigma.
      sigma0 <= sigma /\ sigma <= sigma1 /\
      (!u. sigma0 <= u /\ u <= sigma1 ==> L0 <= Lprof u)
      ==> L0 <= Lprof sigma`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

let C2_THM14_UNIFORM_BAND_OFFAXIS_BOUND = prove
 (`!(c0st:real->real->complex) (Lprof:real->real) L0 sigma0 sigma1 sigma t.
      sigma0 <= sigma /\ sigma <= sigma1 /\ &0 < sigma /\
      (!u. sigma0 <= u /\ u <= sigma1 ==> L0 <= Lprof u) /\
      (!u v. &0 < u ==> Lprof u <= norm(c0st u v))
      ==> L0 <= norm(c0st sigma t)`,
  MESON_TAC[C2_THM14_UNIFORM_BAND_PROFILE_POINT;
            C2_THM14_PROFILE_LOWER_BOUND_ABSTRACT;
            REAL_LE_TRANS]);;

let C2_BAND_CUTOFF_TO_THM10_OFFAXIS_CANONICAL = prove
 (`!(c0st:real->real->complex) (Lprof:real->real)
    zeta X C B L0 sigma0 sigma1 sigma t.
      &0 < X /\ &0 < L0 /\
      sigma0 <= sigma /\ sigma <= sigma1 /\ &0 < sigma /\
      (!u. sigma0 <= u /\ u <= sigma1 ==> L0 <= Lprof u) /\
      (!u v. &0 < u ==> Lprof u <= norm(c0st u v)) /\
      abs(C) <= B * L0 * X
      ==> norm(c2_zx zeta (c2_finite_residual_canonical X C)
               (c0st sigma t) - zeta) <= B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C2_ZX_TRANSFER_FINITE_CANONICAL_BOUND THEN
  EXISTS_TAC `L0:real` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C2_THM14_UNIFORM_BAND_OFFAXIS_BOUND THEN
  EXISTS_TAC `Lprof:real->real` THEN
  EXISTS_TAC `sigma0:real` THEN
  EXISTS_TAC `sigma1:real` THEN
  ASM_REWRITE_TAC[]);;

let C2_BAND_CUTOFF_TO_THM10_OFFAXIS = prove
 (`!(c0st:real->real->complex) (Lprof:real->real)
    zeta X C theta B L0 sigma0 sigma1 sigma t.
      &0 < X /\ norm(theta) <= &1 /\ &0 < L0 /\
      sigma0 <= sigma /\ sigma <= sigma1 /\ &0 < sigma /\
      (!u. sigma0 <= u /\ u <= sigma1 ==> L0 <= Lprof u) /\
      (!u v. &0 < u ==> Lprof u <= norm(c0st u v)) /\
      abs(C) <= B * L0 * X
      ==> norm(c2_zx zeta (c2_finite_residual X C theta)
               (c0st sigma t) - zeta) <= B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC C2_ZX_TRANSFER_FINITE_BOUND THEN
  EXISTS_TAC `L0:real` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC C2_THM14_UNIFORM_BAND_OFFAXIS_BOUND THEN
  EXISTS_TAC `Lprof:real->real` THEN
  EXISTS_TAC `sigma0:real` THEN
  EXISTS_TAC `sigma1:real` THEN
  ASM_REWRITE_TAC[]);;
