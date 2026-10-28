import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BalancedChartEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.AmbientNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.HomogeneousTransformations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartEndomorphismIdentity

/-! # Balanced Chart Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BalancedChartIdentity

noncomputable section

/-! Normalization fixes every balanced degree-zero fraction. The result
is an equality of ring morphisms on the whole affine chart. -/
open scoped BigOperators Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {r m : ℕ}

theorem normalizedBalancedChartEndomorphism_eq_id (hr : 0 < r)
    (i : Fin m) (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r)
    (a : (Fin r → Fin m) → ℕ) (C : Fin m → (Fin r → Fin m) → ℕ)
    (ha : a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight)
    (hC : ∀ z, C z + Frame.CoordinateExponents.frameCoordinateExponent σ e z (c z) = a)
    (hframe : Frame.ChartDenominators.frameDiscriminantExponent σ e ≤ a) :
    BalancedChartEvaluation.normalizedBalancedChartEndomorphism R i σ e c a C ha hC hr hframe = RingHom.id _ := by
  let S := Balanced.DeterminantAlgebra.balancedDeterminantAlgebra R r m
  let g := Balanced.DeterminantGrading.balancedDeterminantGrading R r m i
  let f := Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement R a ha
  let φ := BalancedChartEvaluation.normalizedBalancedPolynomialEvaluation R i σ e c a C ha hC
  let E : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i a ha →ₐ[R] BalancedChart.AmbientFrame.balancedChartAmbientRing R a :=
    Homogeneous.ChartAlgebraEmbedding.homogeneousSubalgebraChartAlgEmbedding S g f
  let v := BalancedChart.AmbientFrame.balancedChartAmbientVectors R a
  let u := Balanced.FrameChartNormalization.balancedFrameChartVectors R i σ e c a C ha hC
  let T := DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun (BalancedChart.AmbientFrame.balancedChartAmbientRing R a) (Fin r))
    (fun j => v (σ j)) (v e)
  obtain ⟨s, _, hs⟩ := BalancedChart.AmbientNormalization.balancedFrameChartVectors_ambient_rescale R i σ e c a C ha hC
  have hE (p : S) : E (φ p) =
      MvPolynomial.aeval (fun jk : Fin m × Fin r => s jk.1 * T (v jk.1) jk.2) p.val := by
    change E (MvPolynomial.aeval (fun jk : Fin m × Fin r => u jk.1 jk.2) p.val) = _
    rw [MvPolynomial.comp_aeval_apply]
    exact congrArg (fun w : Fin m × Fin r → BalancedChart.AmbientFrame.balancedChartAmbientRing R a => MvPolynomial.aeval w p.val)
      (funext fun jk => hs jk.1 jk.2)
  apply Homogeneous.ChartEndomorphismIdentity.homogeneousChartEndomorphism_eq_id S g f
    (Balanced.FrameCoordinatePolynomials.balancedDeterminantMonomialElement_mem_grading R a ha i) φ.toRingHom
    (BalancedChartEvaluation.normalizedBalancedPolynomialEvaluation_denominator_isUnit R i σ e c a C ha hC hr hframe)
  intro k p hp
  have hka : k • a ∈ Balanced.ExponentFiniteGeneration.balancedExponentMonoid DeterminantBlockDegrees.labeledDeterminantWeight :=
    (Balanced.ExponentFiniteGeneration.balancedExponentMonoid _).nsmul_mem ha k
  have hp' : p.val ∈ Balanced.MonomialSpan.balancedMonomialDegreeSpan (R := R) (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R)
      DeterminantBlockDegrees.labeledDeterminantWeight i (Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight (k • a) i) := by
    rw [Balanced.ExponentCompletion.monomialMultiDegree_nsmul]
    exact hp
  have hq : Balanced.MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) (k • a) ∈
      Balanced.MonomialSpan.balancedMonomialDegreeSpan (R := R) (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R)
        DeterminantBlockDegrees.labeledDeterminantWeight i (Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight (k • a) i) :=
    Submodule.subset_span ⟨k • a, ⟨hka, rfl⟩, rfl⟩
  have h := Balanced.HomogeneousTransformations.balancedHomogeneousPolynomial_cross_invariant hr v T s (k • a) hka i
    p.val (Balanced.MonomialAlgebra.exponentMonomial (LabeledDeterminantPolynomials.labeledDeterminantPolynomial R) (k • a)) hp' hq
  rw [NonvanishingMonomialCompletion.exponentMonomial_nsmul, map_pow, map_pow,
    BalancedChart.AmbientNormalization.balancedChartAmbientVectors_aeval, BalancedChart.AmbientNormalization.balancedChartAmbientVectors_aeval] at h
  change E (φ p) * (algebraMap (MvPolynomial (Fin m × Fin r) R)
      (BalancedChart.AmbientFrame.balancedChartAmbientRing R a) f.val) ^ k =
    E (φ f) ^ k * algebraMap (MvPolynomial (Fin m × Fin r) R) (BalancedChart.AmbientFrame.balancedChartAmbientRing R a) p.val
  rw [hE p, hE f]
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.BalancedChartIdentity
