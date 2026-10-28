import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.ComponentComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentCurveCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.TwoTransverseEquationComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.ComparisonGluing
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers

/-! # Coefficient Tangent Independence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CoefficientTangentIndependence.Construction

noncomputable section

/-! Fixed-level curve coefficient tangent centers are independent of both normal-equation choices. -/

universe u

theorem curve_coefficient_tangent_center_independent_of_normal
    {σ k R : Type u} [Field k] [CharZero k] [IsAlgClosed k] [CommRing R]
    [Algebra k R] [Algebra ℚ R]
    [Algebra (MvPolynomial σ k) R] [Algebra.Etale (MvPolynomial σ k) R]
    [IsScalarTower k (MvPolynomial σ k) R] [Fintype σ] [DecidableEq σ]
    (J : Ideal R) (n ℓ : ℕ) (z t : R) (D E : Derivation k R R)
    (hD : D z = 1) (hE : E t = 1)
    (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (ht : t ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hdz : ringKrullDim (R ⧸ Ideal.span {z}) ≤ 1)
    (hdt : ringKrullDim (R ⧸ Ideal.span {t}) ≤ 1) (hlevel : (n + 1).factorial ≤ ℓ + 1)
    (hboundz : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) (ℓ + 1) = ⊤)
    (hboundt : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k t (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)) (ℓ + 1) = ⊤) :
    Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ =
      Coefficient.TangentNaturality.Construction.coefficientTangentCenter k t (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ := by
  let : Algebra.Smooth k (MvPolynomial σ k) := ⟨inferInstance, inferInstance⟩
  let : Algebra.Smooth k R := Algebra.Smooth.comp k (MvPolynomial σ k) R
  let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
  let : Algebra.Smooth k (R ⧸ Ideal.span {t}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one E t hE
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let H := Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n
  let I := Coefficient.TangentNaturality.Construction.coefficientTangentCenter k z H (n + 1) ℓ
  let L := Coefficient.TangentNaturality.Construction.coefficientTangentCenter k t H (n + 1) ℓ
  let T := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n
  have hJI : J ≤ I ^ (n + 1) := (Relative.DifferentialEquiv.Construction.le_relativeHomogenizedIdeal k J n).trans
    (Coefficient.TangentCurveCenter.Construction.coefficientTangentCenter_curve_permissible k D z hD H (n + 1) ℓ hdz hlevel hboundz).1
  have hJL : J ≤ L ^ (n + 1) := (Relative.DifferentialEquiv.Construction.le_relativeHomogenizedIdeal k J n).trans
    (Coefficient.TangentCurveCenter.Construction.coefficientTangentCenter_curve_permissible k E t hE H (n + 1) ℓ hdt hlevel hboundt).1
  have hTI : T ≤ I := Blowups.Ideal.ImageCongruence.Construction.relative_tangent_le_permissible_center k J I n hJI
  have hTL : T ≤ L := Blowups.Ideal.ImageCongruence.Construction.relative_tangent_le_permissible_center k J L n hJL
  apply Pointed.ComparisonGluing.Construction.ideal_eq_of_pointed_flat_comparisons I L
  intro q hq
  let : q.IsMaximal := hq
  by_cases hT : T ≤ q
  · let r : R →ₐ[k] q.ResidueField := IsScalarTower.toAlgHom k R q.ResidueField
    have htransz : ∃ i : σ, i ∉ (∅ : Finset σ) ∧ r (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i z) ≠ 0 := by
      apply Blowups.Etale.TransverseDirection.Construction.exists_transverse_partial_of_boundary_derivation ∅ D r z (by simp)
      rw [hD, map_one]
      exact one_ne_zero
    have htranst : ∃ i : σ, i ∉ (∅ : Finset σ) ∧ r (Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := k) (S := R) i t) ≠ 0 := by
      apply Blowups.Etale.TransverseDirection.Construction.exists_transverse_partial_of_boundary_derivation ∅ E r t (by simp)
      rw [hE, map_one]
      exact one_ne_zero
    have hrz : r z = 0 := Ideal.algebraMap_residueField_eq_zero.mpr (hT hz)
    have hrt : r t = 0 := Ideal.algebraMap_residueField_eq_zero.mpr (hT ht)
    obtain ⟨U, instU, instkU, f, g, v, hf, hg, heq, _, hH, hvf, _, hcenters⟩ :=
      TwoTransverseEquationComparison.Construction.exists_two_transverse_equation_center_comparison J ∅ z t n r htransz htranst hz ht (hrz.trans hrt.symm)
    let : CommRing U := instU
    let : Algebra k U := instkU
    have hcoeff := Blowups.Etale.QuotientNaturality.Construction.relativeCoefficientIdeal_comparison_eq (σ := σ) f g hf hg z t heq H H hH (n + 1)
    have hIL : I.map f.toRingHom = L.map g.toRingHom :=
      Coefficient.TangentNaturality.Construction.coefficientTangentCenter_compared_ambient_ideals f g hf hg z t heq H H (n + 1) ℓ hcoeff
    let Q := RingHom.ker v.toRingHom
    let : Q.IsPrime := Ideal.comap_isPrime v.toRingHom ⊥
    have hQ : Q.comap f.toRingHom = q := by
      ext x
      change v (f x) = 0 ↔ x ∈ q
      rw [hvf x]
      exact Ideal.algebraMap_residueField_eq_zero
    exact ⟨U, instU, f.toRingHom, g.toRingHom, Q, inferInstance,
      (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1, hQ, hIL, hcenters L hJL⟩
  · change ¬ ∀ x : R, x ∈ T → x ∈ q at hT
    push Not at hT
    obtain ⟨a, ha, haq⟩ := hT
    let S := Localization.Away a
    let f := algebraMap R S
    obtain ⟨Q, hQ⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime a ⟨q, inferInstance⟩ haq
    have hIf : I.map f = ⊤ := IdempotentQuotientCenter.Construction.center_map_away_member_eq_top I a (hTI ha)
    have hLf : L.map f = ⊤ := IdempotentQuotientCenter.Construction.center_map_away_member_eq_top L a (hTL ha)
    have hf : f.Etale := RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway a)
    exact ⟨S, inferInstance, f, f, Q.asIdeal, Q.isPrime,
      (RingHom.Etale.iff_flat_and_formallyUnramified.mp hf).1,
      congrArg PrimeSpectrum.asIdeal hQ, hIf.trans hLf.symm, rfl⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Curve.CoefficientTangentIndependence.Construction
