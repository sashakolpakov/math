import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.StandardChartEvaluation

/-! # Section Projections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.SectionProjections

noncomputable section

/-! The homogeneous Segre chart point obtained from normalized row and
column values has precisely those two projective-coordinate maps as its
projections to the actual projective product. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {n m : ℕ} (p : ChartProjections.SegreProjectiveIndex.{u} n m)
section Algebra
variable {B : Type u} [CommRing B] [Algebra R B]
variable (r : Fin (n + 1) → B) (c : Fin (m + 1) → B)
variable (hr : r p.1.down = 1) (hc : c p.2.down = 1)

theorem segreHomogeneousSectionEvaluation_row :
    (TensorCoordinates.segreHomogeneousSectionEvaluation R p r c hr hc).comp (ChartProductAlgebra.segreRowChartAlgebra R p) =
      ProjectiveChart.Algebra.projectiveChartEvaluationAlg r p.1.down hr := by
  apply ProjectiveChart.Algebra.projectiveChartAlgebra_ext p.1.down
  intro a
  change TensorCoordinates.segreHomogeneousSectionEvaluation R p r c hr hc
    (ChartProductAlgebra.segreRowChartAlgebra R p (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.1.down (X a))) = _
  rw [ChartProductAlgebra.segreRowChartAlgebra_coordinate, ProjectiveChart.Algebra.projectiveChartEvaluationAlg_coordinate]
  have h := TensorCoordinates.segreHomogeneousSectionEvaluation_coordinate R p r c hr hc a p.2.down
  rw [hc, mul_one] at h
  exact h

theorem segreHomogeneousSectionEvaluation_column :
    (TensorCoordinates.segreHomogeneousSectionEvaluation R p r c hr hc).comp (ChartProductAlgebra.segreColumnChartAlgebra R p) =
      ProjectiveChart.Algebra.projectiveChartEvaluationAlg c p.2.down hc := by
  apply ProjectiveChart.Algebra.projectiveChartAlgebra_ext p.2.down
  intro b
  change TensorCoordinates.segreHomogeneousSectionEvaluation R p r c hr hc
    (ChartProductAlgebra.segreColumnChartAlgebra R p (HilbertScheme.Presentations.Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.2.down (X b))) = _
  rw [ChartProductAlgebra.segreColumnChartAlgebra_coordinate, ProjectiveChart.Algebra.projectiveChartEvaluationAlg_coordinate]
  have h := TensorCoordinates.segreHomogeneousSectionEvaluation_coordinate R p r c hr hc p.1.down b
  rw [hr, one_mul] at h
  exact h
end Algebra

variable {T : Scheme.{u}} [Algebra R Γ(T, ⊤)]
variable (r : Fin (n + 1) → Γ(T, ⊤)) (c : Fin (m + 1) → Γ(T, ⊤))
variable (hr : r p.1.down = 1) (hc : c p.2.down = 1)

def normalizedSegreSectionMap : T ⟶ ProductComparison.segreEquationScheme (CommRingCat.of R) n m :=
  T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (TensorCoordinates.segreHomogeneousSectionEvaluation R p r c hr hc).toRingHom) ≫
      (ProjectiveScheme.segreHomogeneousChartMap (CommRingCat.of R) p.1 p.2).left

theorem normalizedSegreSectionMap_row :
    normalizedSegreSectionMap R p r c hr hc ≫ ProjectionGluing.segreRowProjection (CommRingCat.of R) n m =
      ProjectiveChart.Evaluation.projectiveChartMap (algebraMap R Γ(T, ⊤)) r p.1.down hr := by
  let φ := TensorCoordinates.segreHomogeneousSectionEvaluation R p r c hr hc
  have h : φ.toRingHom.comp (ChartProductAlgebra.segreRowChartAlgebra R p).toRingHom =
      ProjectiveChart.Evaluation.projectiveChartEvaluation (algebraMap R Γ(T, ⊤)) r p.1.down hr :=
    congrArg AlgHom.toRingHom (segreHomogeneousSectionEvaluation_row R p r c hr hc)
  change (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    (ProjectiveScheme.segreHomogeneousChartMap (CommRingCat.of R) p.1 p.2).left) ≫ _ = _
  rw [Category.assoc, Category.assoc, ProjectionGluing.segreRowProjection_chart]
  change T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (ChartProductAlgebra.segreRowChartAlgebra R p).toRingHom) ≫
      Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R n) (X p.1.down) (isHomogeneous_X R p.1.down) Nat.zero_lt_one = _
  rw [← Spec.map_comp_assoc]
  change T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (φ.toRingHom.comp (ChartProductAlgebra.segreRowChartAlgebra R p).toRingHom)) ≫ _ = _
  rw [h]
  rfl

theorem normalizedSegreSectionMap_column :
    normalizedSegreSectionMap R p r c hr hc ≫ ProjectionGluing.segreColumnProjection (CommRingCat.of R) n m =
      ProjectiveChart.Evaluation.projectiveChartMap (algebraMap R Γ(T, ⊤)) c p.2.down hc := by
  let φ := TensorCoordinates.segreHomogeneousSectionEvaluation R p r c hr hc
  have h : φ.toRingHom.comp (ChartProductAlgebra.segreColumnChartAlgebra R p).toRingHom =
      ProjectiveChart.Evaluation.projectiveChartEvaluation (algebraMap R Γ(T, ⊤)) c p.2.down hc :=
    congrArg AlgHom.toRingHom (segreHomogeneousSectionEvaluation_column R p r c hr hc)
  change (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    (ProjectiveScheme.segreHomogeneousChartMap (CommRingCat.of R) p.1 p.2).left) ≫ _ = _
  rw [Category.assoc, Category.assoc, ProjectionGluing.segreColumnProjection_chart]
  change T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (ChartProductAlgebra.segreColumnChartAlgebra R p).toRingHom) ≫
      Proj.awayι (Projective.ProjectivePresentations.coordinateGrading R m) (X p.2.down) (isHomogeneous_X R p.2.down) Nat.zero_lt_one = _
  rw [← Spec.map_comp_assoc]
  change T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (φ.toRingHom.comp (ChartProductAlgebra.segreColumnChartAlgebra R p).toRingHom)) ≫ _ = _
  rw [h]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.SectionProjections
