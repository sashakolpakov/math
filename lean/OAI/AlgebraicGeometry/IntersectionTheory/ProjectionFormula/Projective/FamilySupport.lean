import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.MatrixFamily
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ScalarComposition

/-! # Family Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilySupport

noncomputable section

/-! The matrix family moves an actual closed projective support.
Its two marked slices are the original support and its prescribed translate. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Polynomial

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.MatrixFamily.Family

theorem inverse_preimage {Y : Scheme} (e : Y ≅ Y) (W : Set Y) : e.inv ⁻¹' W = e.hom '' W := by
  ext x
  constructor
  · intro hx
    refine ⟨e.inv x, hx, ?_⟩
    exact congrArg (fun f : Y ⟶ Y => f x) e.inv_hom_id
  · rintro ⟨y, hy, rfl⟩
    have h : e.inv (e.hom y) = y := congrArg (fun f : Y ⟶ Y => f y) e.hom_inv_id
    change e.inv (e.hom y) ∈ W
    rw [h]
    exact hy

variable {n : ℕ} (A : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)ˣ)

def coefficients : ℂ →+* ProjectionFormula.Polynomial.MatrixPath.Ring A := (algebraMap ℂ[X] (ProjectionFormula.Polynomial.MatrixPath.Ring A)).comp Polynomial.C

def projection : MatrixFamily.Family.space A ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n := Relative.ProjectiveI.Scalars.map (coefficients A) n

theorem specialization_projection (t : ℂ) (ht : (ProjectionFormula.Polynomial.MatrixPath.determinant A).eval t ≠ 0) :
    MatrixFamily.Family.specialization A t ht ≫ projection A = 𝟙 (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := by
  apply Relative.ScalarComposition.map_split
  ext c
  change ProjectionFormula.Polynomial.MatrixPath.evaluation A t ht (algebraMap ℂ[X] (ProjectionFormula.Polynomial.MatrixPath.Ring A) (Polynomial.C c)) = c
  rw [ProjectionFormula.Polynomial.MatrixPath.evaluation_algebraMap, Polynomial.eval_C]

theorem zero_inverse : MatrixFamily.Family.specialization A 0 (ProjectionFormula.Polynomial.MatrixPath.zero_good A) ≫ (MatrixFamily.Family.automorphism A).inv =
    MatrixFamily.Family.specialization A 0 (ProjectionFormula.Polynomial.MatrixPath.zero_good A) := by
  apply (cancel_mono (MatrixFamily.Family.automorphism A).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, MatrixFamily.Family.at_zero]

theorem one_inverse : MatrixFamily.Family.specialization A 1 (ProjectionFormula.Polynomial.MatrixPath.one_good A) ≫ (MatrixFamily.Family.automorphism A).inv =
    (LinearChart.Automorphism.iso A).inv ≫ MatrixFamily.Family.specialization A 1 (ProjectionFormula.Polynomial.MatrixPath.one_good A) := by
  apply (cancel_mono (MatrixFamily.Family.automorphism A).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, MatrixFamily.Family.at_one]
  change MatrixFamily.Family.specialization A 1 (ProjectionFormula.Polynomial.MatrixPath.one_good A) =
    (LinearChart.Automorphism.iso A).inv ≫
      ((LinearChart.Automorphism.iso A).hom ≫ MatrixFamily.Family.specialization A 1 (ProjectionFormula.Polynomial.MatrixPath.one_good A))
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

def support (W : Closeds (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) : Closeds (MatrixFamily.Family.space A) :=
  ⟨((MatrixFamily.Family.automorphism A).inv ≫ projection A) ⁻¹' (W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)),
    W.isClosed.preimage ((MatrixFamily.Family.automorphism A).inv ≫ projection A).continuous⟩

theorem zero_slice (W : Closeds (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) :
    MatrixFamily.Family.specialization A 0 (ProjectionFormula.Polynomial.MatrixPath.zero_good A) ⁻¹' (support A W : Set (MatrixFamily.Family.space A)) = (W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) := by
  change ((MatrixFamily.Family.specialization A 0 (ProjectionFormula.Polynomial.MatrixPath.zero_good A) ≫ (MatrixFamily.Family.automorphism A).inv) ≫ projection A) ⁻¹' (W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) = _
  rw [zero_inverse, specialization_projection]
  rfl

theorem one_slice (W : Closeds (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) :
    MatrixFamily.Family.specialization A 1 (ProjectionFormula.Polynomial.MatrixPath.one_good A) ⁻¹' (support A W : Set (MatrixFamily.Family.space A)) =
      LinearChart.Automorphism.map A '' (W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) := by
  change ((MatrixFamily.Family.specialization A 1 (ProjectionFormula.Polynomial.MatrixPath.one_good A) ≫ (MatrixFamily.Family.automorphism A).inv) ≫ projection A) ⁻¹' (W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) = _
  rw [one_inverse, Category.assoc, specialization_projection, Category.comp_id]
  exact inverse_preimage (LinearChart.Automorphism.iso A) (W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n))

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilySupport
