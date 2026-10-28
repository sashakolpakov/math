import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.EvaluationNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BalancedChartIdentity

/-! # Normalized Representatives -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.NormalizedRepresentatives

noncomputable section

/-! Every algebra-valued point of the balanced chart has an explicit
normalized vector configuration representing it. -/
open scoped Classical
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {A : Type v} [CommRing A] [Algebra R A] {r m : ℕ}

private theorem mappedBalancedFrame_normalizes
    (i : Fin m) (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r)
    (a : (Fin r → Fin m) → ℕ) (C : Fin m → (Fin r → Fin m) → ℕ)
    (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : ∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a)
    (hframe : Frame.ChartDenominators.frameDiscriminantExponent σ e ≤ a)
    (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i a ha →ₐ[R] A) :
    (∀ z, ρ (Balanced.FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC z (c z)) = 1) ∧
    (∀ k, ρ (Balanced.FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC e k) = 1) ∧
    ∀ j k, ρ (Balanced.FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC (σ j) k) =
      if j = k then 1 else 0 := by
  have hn := Balanced.FrameChartNormalization.balancedFrameChartVectors_normalizes R i σ e c a C ha hC hframe
  refine ⟨?_, ?_, ?_⟩
  · intro z
    exact (congrArg ρ.toRingHom
      (Balanced.FrameChartNormalization.balancedFrameChartVectors_selected R i σ e c a C ha hC z)).trans ρ.toRingHom.map_one
  · intro k
    exact (congrArg ρ.toRingHom (hn.1 k)).trans ρ.toRingHom.map_one
  · intro j k
    rw [hn.2 j k]
    split_ifs
    · exact ρ.map_one
    · exact ρ.map_zero

private theorem map_configuration_evaluation {B : Type*} [CommRing B] [Algebra R B]
    (i : Fin m) (v : Fin m → Fin r → B)
    (a : (Fin r → Fin m) → ℕ) (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) a))
    (ρ : B →ₐ[R] A) :
    ∃ hw : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (fun z k => ρ (v z k))) a),
      Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i (fun z k => ρ (v z k)) a ha hw =
        ρ.toRingHom.comp (Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v a ha hv) := by
  have hpoly : ρ (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) a) =
      Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (fun z k => ρ (v z k))) a := by
    change ρ.toRingHom (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) a) = _
    rw [MonomialExponentExtension.exponentMonomial_map]
    congr 1
    funext τ
    exact LabeledDeterminantPolynomials.labeledDeterminant_map ρ.toRingHom τ v
  have hw := hpoly ▸ hv.map ρ.toMonoidHom
  exact ⟨hw, (EvaluationNaturality.balancedConfigurationChartEvaluation_comp i v a ha hv ρ hw).symm⟩

private theorem mappedBalancedFrame_evaluation (hr : 0 < r)
    (i : Fin m) (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r)
    (a : (Fin r → Fin m) → ℕ) (C : Fin m → (Fin r → Fin m) → ℕ)
    (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : ∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a)
    (hframe : Frame.ChartDenominators.frameDiscriminantExponent σ e ≤ a)
    (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i a ha →ₐ[R] A) :
    let w : Fin m → Fin r → A := fun z k =>
      ρ (Balanced.FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC z k)
    ∃ hw : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) a),
      Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i w a ha hw = ρ.toRingHom := by

  let u := Balanced.FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC
  have hunit : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ u) a) :=
    Normalized.BalancedDenominatorUnit.normalizedBalancedDenominator_isUnit R hr i σ e c a C ha hC hframe
  have hid : Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i u a ha hunit = RingHom.id _ :=
    Normalized.BalancedChartIdentity.normalizedBalancedChartEndomorphism_eq_id R hr i σ e c a C ha hC hframe
  obtain ⟨hw, heq⟩ := map_configuration_evaluation R i u a ha hunit ρ
  rw [hid, RingHom.comp_id] at heq
  exact ⟨hw, heq⟩

theorem balancedChartPoint_has_normalized_configuration (hr : 0 < r)
    (i : Fin m) (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r)
    (a : (Fin r → Fin m) → ℕ) (C : Fin m → (Fin r → Fin m) → ℕ)
    (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : ∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a)
    (hframe : Frame.ChartDenominators.frameDiscriminantExponent σ e ≤ a)
    (ρ : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i a ha →ₐ[R] A) :
    ∃ (w : Fin m → Fin r → A)
      (hw : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) a)),
      Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i w a ha hw = ρ.toRingHom ∧
      (∀ z, w z (c z) = 1) ∧ (∀ k, w e k = 1) ∧
      ∀ j k, w (σ j) k = if j = k then 1 else 0 := by
  let w : Fin m → Fin r → A := fun z k =>
    ρ (Balanced.FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC z k)
  obtain ⟨hw, heq⟩ := mappedBalancedFrame_evaluation R hr i σ e c a C ha hC hframe ρ
  have hn := mappedBalancedFrame_normalizes R i σ e c a C ha hC hframe ρ
  exact ⟨w, hw, heq, hn.1, hn.2.1, hn.2.2⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.NormalizedRepresentatives
