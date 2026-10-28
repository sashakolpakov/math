import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.ProjectiveChartCoordinateChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.QuotientCoordinateChart
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientBot

/-! # Linear Projective Identity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.LinearProjectiveIdentity

noncomputable section

/-! Multiplication of all homogeneous coordinates by one unit
induces the identity on the actual projective scheme. The proof
uses normalized chart maps, including their structure sheaves. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientBot.GradedHilbert
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {n : ℕ}
variable (e : (Fin (n + 1) →₀ R) ≃ₗ[R] (Fin (n + 1) →₀ R)) (a : Rˣ)
variable (he : e.symm.toLinearMap = (a : R) • LinearMap.id)

include he in
theorem gradedCoordinateValues_inverse_scalar {B : Type u} [CommRing B]
    (c : R →+* B) (v : Fin (n + 1) → B) (j : Fin (n + 1)) :
    GradedCoordinateEvaluation.gradedCoordinateValues (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.symm.toLinearMap) c v j = c a * v j := by
  change MvPolynomial.eval₂Hom c v (Linear.CoordinateSubstitution.polynomialLinearSubstitution e.symm.toLinearMap (MvPolynomial.X j)) = _
  rw [Linear.CoordinateSubstitution.polynomialLinearSubstitution_X, he]
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [map_smul, Linear.CoordinateSubstitution.linearCoordinatePolynomial_single, one_smul, MvPolynomial.smul_eq_C_mul,
    map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']

include a he in
theorem projectiveChartMap_scalar_linearCoordinates {X : Scheme.{u}}
    (c : R →+* Γ(X, ⊤)) (v : Fin (n + 1) → Γ(X, ⊤)) (i : Fin (n + 1)) (hi : v i = 1) :
    ProjectiveChart.Evaluation.projectiveChartMap c v i hi ≫ (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n e).hom.left = ProjectiveChart.Evaluation.projectiveChartMap c v i hi := by
  let b : Γ(X, ⊤)ˣ := Units.map c.toMonoidHom a
  have hb : GradedCoordinateEvaluation.gradedCoordinateValues (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.symm.toLinearMap) c v i = b := by
    rw [gradedCoordinateValues_inverse_scalar e a he, hi, mul_one]
    rfl
  have hv : (fun k => (↑b⁻¹ : Γ(X, ⊤)) *
      GradedCoordinateEvaluation.gradedCoordinateValues (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.symm.toLinearMap) c v k) = v := by
    funext k
    rw [gradedCoordinateValues_inverse_scalar e a he]
    change (↑b⁻¹ : Γ(X, ⊤)) * ((b : Γ(X, ⊤)) * v k) = v k
    rw [← mul_assoc, b.inv_mul, one_mul]
  exact (Linear.ProjectiveChartCoordinateChange.projectiveChartMap_linearCoordinates e c v i i hi b hb).trans
    (Framed.ProjectiveMaps.projectiveChartMap_congr c hv i _ hi)

include a he in
theorem affineLinearCoordinateIso_eq_id_of_inverse_scalar :
    (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n e).hom.left = 𝟙 _ := by
  let I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) := ⊥
  apply (cancel_epi (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I)).mp
  erw [Category.comp_id]
  let C : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).OpenCover := {
    I₀ := Fin (n + 1)
    X i := (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).toScheme
    f i := (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x => ?_, inferInstance⟩
      obtain ⟨i, hi⟩ := ProjectiveTwisting.Bundle.projectiveTwistingCover I x
      exact ⟨i.down, ⟨x, hi⟩, rfl⟩ }
  apply C.hom_ext
  intro i
  change (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).ι ≫
    (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ≫ (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n e).hom.left) =
      (ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}).ι ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I
  rw [← Category.assoc, Canonical.QuotientCoordinateChart.projectiveQuotientInclusion_coordinateChart]
  exact projectiveChartMap_scalar_linearCoordinates e a he _ _ i _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.LinearProjectiveIdentity
