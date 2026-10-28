import OAI.AlgebraicGeometry.Divisors.LineBundles.SurfaceRationalOrderIntersection
import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.LocalDivisor

/-! # Surface Prime Curve -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.SurfacePrimeCurve.BundleCycles

noncomputable section

/-!
# LineBundleCycles: every minimal prime section of a local surface is an actual local curve

Krull's principal ideal theorem excludes the maximal ideal among the
minimal primes of a nonzero equation on a two-dimensional local domain.
The quotient is consequently one-dimensional, including singular curves.
-/

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsDomain R] in
theorem surfaceMinimalPrime_ne_maximal (b : R) (hdim : ringKrullDim R = 2)
    (P : Ideal R) (hP : P ∈ (Ideal.span {b}).minimalPrimes) :
    P ≠ IsLocalRing.maximalIdeal R := by
  intro he
  have hh : P.height ≤ (1 : ℕ∞) :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {b}) P hP
  have hm : ((IsLocalRing.maximalIdeal R).height : WithBot ℕ∞) ≤ 1 :=
    WithBot.coe_le_coe.mpr (he ▸ hh)
  rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdim] at hm
  exact (by norm_num : ¬ (2 : WithBot ℕ∞) ≤ 1) hm

theorem surfacePrimeQuotient_dimension (b : R) (hb : b ≠ 0) (hdim : ringKrullDim R = 2)
    (P : Ideal R) (hP : P ∈ (Ideal.span {b}).minimalPrimes) : ringKrullDim (R ⧸ P) = 1 := by
  let : P.IsPrime := hP.isPrime
  let : IsLocalRing (R ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  let : Ring.KrullDimLE 1 (R ⧸ P) :=
    SurfaceRationalOrderIntersection.BundleCycles.surfacePrimeSupport_krullDimLE b hb hdim P (hP.le (Ideal.subset_span (Set.mem_singleton b)))
  have hfield : ¬ IsField (R ⧸ P) := fun hf =>
    surfaceMinimalPrime_ne_maximal b hdim P hP
      (IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField P hf))
  have hn : IsLocalRing.maximalIdeal (R ⧸ P) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField inferInstance hfield
  have hh : (1 : ℕ∞) ≤ (IsLocalRing.maximalIdeal (R ⧸ P)).height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hn)
  apply le_antisymm (Ring.krullDimLE_iff.mp inferInstance)
  exact (WithBot.coe_le_coe.mpr hh).trans_eq IsLocalRing.maximalIdeal_height_eq_ringKrullDim

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.SurfacePrimeCurve.BundleCycles
