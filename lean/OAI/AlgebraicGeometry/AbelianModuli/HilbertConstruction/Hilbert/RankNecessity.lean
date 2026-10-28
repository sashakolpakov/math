import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedFlatIdeals
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedReconstruction

/-! # Rank Necessity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An actual field Hilbert ideal forces the finite numerical rank test used by the parameter construction. -/

universe u

variable {K : Type u} [Field K] {n N : ℕ} {P : Polynomial ℚ}

theorem SaturatedFlatIdeals.SaturatedFlatHilbertIdeal.generatedRankTest (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal K n P)
    (hI : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.ideal.toIdeal P) (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N) :
    Generated.RankTests.GeneratedHilbertRankTest n P N := by
  let B := max N (Truncated.PolynomialTest.truncatedHilbertTestBound n N)
  let D := I.generatedData N hN B
  have hNB : N ≤ B := Nat.le_max_left _ _
  have hs : HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation D.val.generatedIdeal = I.ideal :=
    Uniform.GeneratedReconstruction.uniformGeneratedTruncation_saturation I.ideal I.saturated P I.hilbert N hN B hNB
  have hD : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial D.val.generatedIdeal.toIdeal P := by
    apply (HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff D.val.generatedIdeal P).mp
    rw [hs]
    exact hI
  have ht := (D.val.generated_hilbertPolynomial_finite_test N hNB D.property (Nat.le_max_right _ _) P).mp hD
  refine ⟨ht.1, ?_⟩
  intro i
  have hi := ht.2 i
  rw [Uniform.GeneratedCoordinates.generatedHilbertRanks, ite_eq_right (Nat.not_lt.mpr
    ((Generated.RankTests.generatedHilbertTestDegree_ge n N).trans (Nat.le_add_right _ _)))] at hi
  exact hi

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
