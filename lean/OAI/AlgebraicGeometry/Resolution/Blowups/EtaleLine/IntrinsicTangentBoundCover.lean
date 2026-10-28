import OAI.AlgebraicGeometry.Resolution.Blowups.Curve.TangentBoundedChoices

/-! # Intrinsic Tangent Bound Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.IntrinsicTangentBoundCover.Construction

noncomputable section

/-! Intrinsic coefficient ideals supply all lower-bound charts of the actual line-tangent blowup. -/

open _root_.Polynomial

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra HorizontalDerivation.Construction.etaleLine_polynomial_originalScalarTower

variable (k : Type u) {H R : Type u}
    [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [CommRing R]
    [Algebra k H] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
    [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]
    [Algebra.Smooth k H] [Algebra ℚ R] [IsNoetherianRing R]

theorem etaleLine_intrinsic_tangent_bounded_generators
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H)
    (J : Ideal R) (n ℓ : ℕ)
    (hz : algebraMap H[X] R X ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n)
    (hdim : ringKrullDim H ≤ 1) (hlevel : (n + 1).factorial ≤ ℓ + 1)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap H[X] R X) J (n + 1)) (ℓ + 1) = ⊤) :
    let I := Coefficient.TangentNaturality.Construction.coefficientTangentCenter k (algebraMap H[X] R X) J (n + 1) ℓ
    ∃ (κ : Type u) (g : κ → I),
      Ideal.span (Set.range (fun a => (g a).val)) = I ∧
      ∀ a, ∃ B : Component.CenterChoice.Construction.ComponentCenterChoice k (Blowup.Charts.Construction.blowupChart I (g a))
        (ControlledTransform.Construction.blowupControlledTransform I J (n + 1) (g a)) n, B.HasBound ℓ := by
  let C := Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap H[X] R X) J (n + 1)
  let K := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (C.map e.toRingHom) ℓ
  let I := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K
  let p : J → R := Subtype.val
  have hp : Ideal.span (Set.range p) = J := by rw [Subtype.range_val, Ideal.span_eq]
  have hl : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
      (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R)) (algebraMap H[X] R X) p (n + 1) ≤ C := by
    simpa only [hp] using Relative.CoefficientFamilyInterval.Construction.weightedCoordinateDerivativeFamilyIdeal_le_relative k
      (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R)) (algebraMap H[X] R X) p (n + 1)
  have hu : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap H[X] R X) (Ideal.span (Set.range p)) (n + 1) := by
    rw [hp]
  have hzp : algebraMap H[X] R X ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span (Set.range p)) n := hp.symm ▸ hz
  have hchoices := Curve.TangentBoundedChoices.Construction.etaleLine_curve_tangent_bounded_choices k e p n ℓ C hl hu hzp hdim hlevel hbound
  rw [hp] at hchoices
  have hcenter : I = Coefficient.TangentNaturality.Construction.coefficientTangentCenter k (algebraMap H[X] R X) J (n + 1) ℓ :=
    TangentCenter.Construction.etaleLine_tangent_center_eq_preimage k e C ℓ
  change ∃ (κ : Type u) (g : κ → Coefficient.TangentNaturality.Construction.coefficientTangentCenter k (algebraMap H[X] R X) J (n + 1) ℓ), _
  rw [← hcenter]
  exact ⟨Option K, BlowupCover.Construction.etaleLineChartGenerator K, BlowupCover.Construction.etaleLineChartGenerator_span K, hchoices⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.IntrinsicTangentBoundCover.Construction
