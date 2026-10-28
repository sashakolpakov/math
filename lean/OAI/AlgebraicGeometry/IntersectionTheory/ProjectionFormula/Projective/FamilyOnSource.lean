import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilySupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Cone.MovingPosition

/-! # Family On Source -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyOnSource

noncomputable section

/-! Pull the actual projective support family back along a fixed
smooth projective embedding, retaining exact endpoint intersections. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Family

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.MatrixPath

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
  (A : (Matrix (Fin (X.ambientDimension + 1)) (Fin (X.ambientDimension + 1)) ℂ)ˣ)

abbrev space : Scheme := pullback (FamilySupport.Family.projection A) X.embedding

def toAmbient : space X A ⟶ MatrixFamily.Family.space A := pullback.fst _ _

def toSource : space X A ⟶ X.carrier := pullback.snd _ _

def specialization (t : ℂ) (ht : (Polynomial.MatrixPath.determinant A).eval t ≠ 0) : X.carrier ⟶ space X A :=
  pullback.lift (X.embedding ≫ MatrixFamily.Family.specialization A t ht) (𝟙 X.carrier) (by
    rw [Category.assoc, FamilySupport.Family.specialization_projection, Category.comp_id, Category.id_comp])

theorem specialization_ambient (t : ℂ) (ht : (Polynomial.MatrixPath.determinant A).eval t ≠ 0) :
    specialization X A t ht ≫ toAmbient X A = X.embedding ≫ MatrixFamily.Family.specialization A t ht :=
  pullback.lift_fst _ _ _

theorem specialization_source (t : ℂ) (ht : (Polynomial.MatrixPath.determinant A).eval t ≠ 0) :
    specialization X A t ht ≫ toSource X A = 𝟙 X.carrier := pullback.lift_snd _ _ _

def support (W : Closeds (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) : Closeds (space X A) :=
  ⟨toAmbient X A ⁻¹' (FamilySupport.Family.support A W : Set (MatrixFamily.Family.space A)),
    (FamilySupport.Family.support A W).isClosed.preimage (toAmbient X A).continuous⟩

theorem zero_slice (W : Closeds (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) :
    specialization X A 0 (Polynomial.MatrixPath.zero_good A) ⁻¹' (support X A W : Set (space X A)) =
      X.embedding ⁻¹' (W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) := by
  change (specialization X A 0 (Polynomial.MatrixPath.zero_good A) ≫ toAmbient X A) ⁻¹'
    (FamilySupport.Family.support A W : Set (MatrixFamily.Family.space A)) = _
  rw [specialization_ambient]
  change X.embedding ⁻¹' (MatrixFamily.Family.specialization A 0 (Polynomial.MatrixPath.zero_good A) ⁻¹'
    (FamilySupport.Family.support A W : Set (MatrixFamily.Family.space A))) = _
  rw [FamilySupport.Family.zero_slice]

theorem one_slice (W : Closeds (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension)) :
    specialization X A 1 (Polynomial.MatrixPath.one_good A) ⁻¹' (support X A W : Set (space X A)) =
      X.embedding ⁻¹' (LinearChart.Automorphism.map A '' (W : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace X.ambientDimension))) := by
  change (specialization X A 1 (Polynomial.MatrixPath.one_good A) ≫ toAmbient X A) ⁻¹'
    (FamilySupport.Family.support A W : Set (MatrixFamily.Family.space A)) = _
  rw [specialization_ambient]
  change X.embedding ⁻¹' (MatrixFamily.Family.specialization A 1 (Polynomial.MatrixPath.one_good A) ⁻¹'
    (FamilySupport.Family.support A W : Set (MatrixFamily.Family.space A))) = _
  rw [FamilySupport.Family.one_slice]

end Family

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.FamilyOnSource
