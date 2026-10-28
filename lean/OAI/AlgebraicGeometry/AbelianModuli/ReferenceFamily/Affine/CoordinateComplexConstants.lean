import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoordinateSectionMap
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.ComplexConstants

/-! # Coordinate Complex Constants -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoordinateComplexConstants

noncomputable section

/-! The specified complex scalars of actual affine coordinate
algebras are the actual global constants from the structure morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem complexGlobalSectionMap_natural {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (f : X ⟶ Y) (c : ℂ) :
    f.left.appTop (Open.ComplexConstants.complexGlobalSectionMap Y c) = Open.ComplexConstants.complexGlobalSectionMap X c := by
  have h := congrArg (fun g : X.left ⟶ Foundations.Scheme.ProjectiveSpace.complexBase => g.appTop ((Scheme.ΓSpecIso (.of ℂ)).inv c)) f.w
  rw [Scheme.Hom.comp_appTop] at h
  exact h

theorem affineCoordinateComplexAlgebraMap_eq (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left] :
    algebraMap ℂ (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ X) = algebraMap ℂ Γ(X.left, ⊤) := by
  have he : X.left.isoSpec.inv ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ X))) :=
    (HilbertConstruction.Affine.OverChartPoints.affineOverIso ℂ X).inv.w
  have hn : X.left.isoSpec.inv ≫ X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ Γ(X.left, ⊤))) :=
    (Foundations.Scheme.AffineSchemeComplexPoints.affineOverIso X).inv.w
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective (he.symm.trans hn))

theorem affineCoordinateComplexConstant (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] [IsReduced X.left] (c : ℂ) :
    algebraMap ℂ (HilbertConstruction.Affine.OverChartPoints.affineOverAlgebra ℂ X) c = Open.ComplexConstants.complexGlobalSectionMap X c :=
  (RingHom.congr_fun (affineCoordinateComplexAlgebraMap_eq X) c).trans (ComplexConstants.affineComplexConstant_structure X c)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.CoordinateComplexConstants
