import OAI.AlgebraicGeometry.Albanese.Construction.ProjectiveCoordinates
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectivePointSurjective

/-! # Affine Coordinates -/

namespace OAI.AlgebraicGeometry.Albanese.Construction.AffineCoordinates

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization

/-- Global section evaluation on an affine spectrum is the original ring map. -/
theorem pointEvaluate_SpecMap {R : CommRingCat} (φ : R ⟶ .of ℂ) (r : R) :
    ProjectiveCoordinates.pointEvaluate (Spec.map φ) ((Scheme.ΓSpecIso R).inv r) = φ r := by
  change ((Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop ≫ (Scheme.ΓSpecIso (.of ℂ)).hom) r = φ r
  rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- The normalized homogeneous coordinates on an actual polynomial chart. -/
def affineChartSections (n : ℕ) (i : Fin (n + 1)) :
    Fin (n + 1) → Γ(Spec (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i)), ⊤) :=
  fun k => (Scheme.ΓSpecIso (.of (Foundations.Scheme.ProjectiveChartToPolynomial.projectiveChartPolynomial n i))).inv
    (Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.dehomogenize i (MvPolynomial.X k))

@[simp]
theorem affineChartSections_self (n : ℕ) (i : Fin (n + 1)) :
    affineChartSections n i i = 1 := by simp [affineChartSections]

/-- Evaluating the chart sections inserts one in the omitted coordinate. -/
theorem affineChartSections_evaluate (n : ℕ) (i : Fin (n + 1))
    (a : {j : Fin (n + 1) // j ≠ i} → ℂ) :
    (fun k => ProjectiveCoordinates.pointEvaluate (Spec.map (CommRingCat.ofHom (MvPolynomial.eval a)))
      (affineChartSections n i k)) = Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i a := by
  funext k
  rw [affineChartSections, pointEvaluate_SpecMap]
  simpa using Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.eval_dehomogenize i (MvPolynomial.X k) a

set_option backward.isDefEq.respectTransparency false in
/-- The normalized-coordinate construction recovers the genuine projective
affine-chart inclusion, as a scheme morphism. -/
theorem projectiveMapOfCoordinates_affineChart (n : ℕ) (i : Fin (n + 1)) :
    ProjectiveCoordinates.projectiveMapOfCoordinates (Foundations.Scheme.ProjectiveChart.projectiveChartPolynomialToBase n i)
        (affineChartSections n i) i (affineChartSections_self n i) =
      Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i := by
  let S := Over.mk (Foundations.Scheme.ProjectiveChart.projectiveChartPolynomialToBase n i)
  let P := Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  have : LocallyOfFiniteType S.hom := by
    change LocallyOfFiniteType (Foundations.Scheme.ProjectiveChart.projectiveChartPolynomialToBase n i)
    rw [← Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap_over]
    infer_instance
  have : IsReduced S.left := by dsimp [S]; infer_instance
  have : LocallyOfFiniteType P.hom := by dsimp [P]; infer_instance
  have : IsSeparated P.hom := by dsimp [P]; infer_instance
  let f : S ⟶ P := Over.homMk _
    (ProjectiveCoordinates.projectiveMapOfCoordinates_over _ _ _ (affineChartSections_self n i))
  let g : S ⟶ P := Over.homMk _ (Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap_over n i)
  have heq : f = g := by
    apply ClosedPoints.hom_ext_of_points S P f g
    intro p
    apply Over.OverMorphism.ext
    change p.left ≫ ProjectiveCoordinates.projectiveMapOfCoordinates (Foundations.Scheme.ProjectiveChart.projectiveChartPolynomialToBase n i)
      (affineChartSections n i) i (affineChartSections_self n i) = p.left ≫ Foundations.Scheme.ProjectiveChart.projectiveAffineChartMap n i
    rw [ProjectiveCoordinates.projectiveMapOfCoordinates_point (Foundations.Scheme.ProjectiveChart.projectiveChartPolynomialToBase n i) p.left p.w _ _ _
      (ProjectiveCoordinates.pointEvaluate_tuple_ne_zero p.left _ i (affineChartSections_self n i))]
    obtain ⟨a, ha⟩ := Foundations.Scheme.ProjectivePointSurjective.affinePolynomialPoint_eq_eval p.left p.w
    have hv : (fun k => ProjectiveCoordinates.pointEvaluate p.left (affineChartSections n i k)) = Foundations.Scheme.DehomogenizationC.Algebraic.Dehomogenization.insertOne i a := by
      rw [ha]
      exact affineChartSections_evaluate n i a
    rw [ha, Foundations.Scheme.ProjectiveChartPoint.projectiveAffineChartMap_eval_eq_vectorPoint n i a (Foundations.Scheme.ProjectiveChartPoint.insertOne_ne_zero n i a)]
    congr 1
    exact affineChartSections_evaluate n i a
  exact congrArg Over.Hom.left heq

end

end OAI.AlgebraicGeometry.Albanese.Construction.AffineCoordinates
