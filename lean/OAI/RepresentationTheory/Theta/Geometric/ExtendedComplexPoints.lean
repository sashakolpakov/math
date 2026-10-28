import OAI.RepresentationTheory.Theta.Geometric.TangentSources
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs

/-! # Extended Complex Points -/

namespace OAI.RepresentationTheory.Theta.Geometric.ExtendedComplexPoints

noncomputable section

/-! The extended residue-field point is the original complex point
precomposed with its actual structural morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs
open _root_.CategoryTheory.CartesianMonoidalCategory

variable (F : Type) [Field F] [Algebra ℂ F]

def extendedComplexPoint {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    (Over.map (LieFieldTests.fieldBaseMap ℂ F)).obj (Over.mk (𝟙 (Spec (.of F)))) ⟶ X :=
  toUnit _ ≫ p

variable (A : Type) [CommRing A] [Algebra ℂ A] [Algebra A ℂ]
  [IsScalarTower ℂ A ℂ] [Algebra A F] [IsScalarTower ℂ A F] [IsScalarTower A ℂ F]

theorem geometricAffineBasePoint_extended :
    (TangentSources.geometricFieldPointIso ℂ F).inv ≫ AffineTangents.geometricAffineBasePoint ℂ A F =
      extendedComplexPoint F (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv A (IsScalarTower.toAlgHom ℂ A ℂ)) := by
  apply Over.OverMorphism.ext
  change 𝟙 (Spec (.of F)) ≫ Spec.map (CommRingCat.ofHom (algebraMap A F)) =
    (𝟙 (Spec (.of F)) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ F))) ≫
      (𝟙 (Spec (.of ℂ)) ≫ Spec.map (CommRingCat.ofHom (algebraMap A ℂ)))
  simp only [Category.id_comp]
  have hr : CommRingCat.ofHom (algebraMap A ℂ) ≫ CommRingCat.ofHom (algebraMap ℂ F) =
      CommRingCat.ofHom (algebraMap A F) :=
    CommRingCat.hom_ext (IsScalarTower.algebraMap_eq A ℂ F).symm
  exact (congrArg Spec.map hr).symm.trans (Spec.map_comp _ _)

end

end OAI.RepresentationTheory.Theta.Geometric.ExtendedComplexPoints
