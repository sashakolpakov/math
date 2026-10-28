import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.IntrinsicCoefficientCenter

/-! # Tangent Curve Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentCurveCenter.Construction

noncomputable section

/-! The intrinsic coefficient tangent construction is an actual smooth permissible center in coefficient dimension one. -/

universe u

theorem coefficientTangentCenter_curve_permissible
    (k : Type u) [Field k] [IsAlgClosed k] {R : Type u} [CommRing R]
    [Algebra k R] [Algebra ℚ R] [IsNoetherianRing R]
    (E : Derivation k R R) (z : R) (hz : E z = 1) (J : Ideal R) (b n : ℕ)
    [Algebra.Smooth k (R ⧸ Ideal.span {z})]
    (hd : ringKrullDim (R ⧸ Ideal.span {z}) ≤ 1) (hbn : b.factorial ≤ n + 1)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b) (n + 1) = ⊤) :
    J ≤ (TangentNaturality.Construction.coefficientTangentCenter k z J b n) ^ b ∧
      Algebra.Smooth k (R ⧸ TangentNaturality.Construction.coefficientTangentCenter k z J b n) := by
  let p : J → R := Subtype.val
  have hspan : Ideal.span (Set.range p) = J := by rw [Subtype.range_val, Ideal.span_eq]
  have hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal E z p b ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b := by
    have h := Relative.CoefficientFamilyInterval.Construction.weightedCoordinateDerivativeFamilyIdeal_le_relative k E z p b
    rwa [hspan] at h
  obtain ⟨_, hperm, hsmooth, _, _⟩ := Curve.IntrinsicCoefficientCenter.Construction.curve_intrinsic_coefficient_center_lift k E z hz p b n hd
    (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z J b) hlow hbn hbound
  rw [hspan] at hperm
  exact ⟨hperm, hsmooth⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.TangentCurveCenter.Construction
