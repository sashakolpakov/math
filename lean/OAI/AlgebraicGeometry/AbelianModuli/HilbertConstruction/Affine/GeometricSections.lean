import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionCounit
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AdjunctionSectionNormalization
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Geometric Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GeometricSections.AffineGeometricSections

noncomputable section

/-! The actual affine scalar-extension formula, normalized against the canonical pullback adjunction unit. -/
open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
universe u
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionCounit.AffineSectionAdjunction
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
variable (M : X.Modules) [M.IsQuasicoherent]

def leftComparison : SectionAdjunction.AffineSectionAdjunction.left X ⋙ Scheme.Modules.pullback f ≅
    ModuleCat.extendScalars f.appTop.hom ⋙ SectionAdjunction.AffineSectionAdjunction.left Y :=
  AdjunctionSectionNormalization.AdjunctionSections.leftComparison (SectionAdjunction.AffineSectionAdjunction.adjunction X) (SectionAdjunction.AffineSectionAdjunction.adjunction Y)
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (ModuleCat.extendRestrictScalarsAdj f.appTop.hom) (SectionAdjunction.AffineSectionAdjunction.pushforwardIso f)

def iso : (ModuleCat.extendScalars f.appTop.hom).obj ((SectionAdjunction.AffineSectionAdjunction.sections X).obj M) ≅
    (SectionAdjunction.AffineSectionAdjunction.sections Y).obj ((Scheme.Modules.pullback f).obj M) := by
  have : IsIso (SectionAdjunction.AffineSectionAdjunction.adjunction Y).unit :=
    @Adjunction.unit_isIso_of_L_fully_faithful _ _ _ _ (SectionAdjunction.AffineSectionAdjunction.left Y) (SectionAdjunction.AffineSectionAdjunction.sections Y)
      (SectionAdjunction.AffineSectionAdjunction.adjunction Y) (SectionAdjunction.AffineSectionAdjunction.left_full Y) (SectionAdjunction.AffineSectionAdjunction.left_faithful Y)
  exact (asIso (SectionAdjunction.AffineSectionAdjunction.adjunction Y).unit).app _ ≪≫ (SectionAdjunction.AffineSectionAdjunction.sections Y).mapIso
    (((leftComparison f).app _).symm ≪≫ (Scheme.Modules.pullback f).mapIso (SectionCounit.AffineSectionAdjunction.counitIso X M))

theorem iso_eq_sectionsMap : (iso f M).hom =
    AdjunctionSectionNormalization.AdjunctionSections.sectionsMap (SectionAdjunction.AffineSectionAdjunction.adjunction X) (SectionAdjunction.AffineSectionAdjunction.adjunction Y)
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (ModuleCat.extendRestrictScalarsAdj f.appTop.hom) (SectionAdjunction.AffineSectionAdjunction.pushforwardIso f) M := by
  rw [AdjunctionSectionNormalization.AdjunctionSections.sectionsMap, Adjunction.homEquiv_unit]
  rfl

theorem normalization : (ModuleCat.extendRestrictScalarsAdj f.appTop.hom).homEquiv _ _ (iso f M).hom =
    (SectionAdjunction.AffineSectionAdjunction.sections X).map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (SectionAdjunction.AffineSectionAdjunction.pushforwardIso f).hom.app ((Scheme.Modules.pullback f).obj M) := by
  rw [iso_eq_sectionsMap]
  exact AdjunctionSectionNormalization.AdjunctionSections.normalization _ _ _ _ _ M

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GeometricSections.AffineGeometricSections
