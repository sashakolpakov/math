import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionIs
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AdjunctionSectionsLeft
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.PullbackSectionTensor

/-! # Affine Geometric -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineGeometric

noncomputable section

/-! The canonical affine pullback formula for actual schemes and their global sections. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped ChangeOfRings

universe u

namespace Construction.AffineGeometricSections

open OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineSectionIs.Construction.AffineSectionAdjunction

variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
variable (M : X.Modules) [M.IsQuasicoherent]

def leftComparison : AffineSectionIs.Construction.AffineSectionAdjunction.left X ⋙ Scheme.Modules.pullback f ≅
    ModuleCat.extendScalars f.appTop.hom ⋙ AffineSectionIs.Construction.AffineSectionAdjunction.left Y :=
  AdjunctionSectionsLeft.Construction.AdjunctionSections.leftComparison (AffineSectionIs.Construction.AffineSectionAdjunction.adjunction X) (AffineSectionIs.Construction.AffineSectionAdjunction.adjunction Y)
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (ModuleCat.extendRestrictScalarsAdj f.appTop.hom) (AffineSectionIs.Construction.AffineSectionAdjunction.pushforwardIso f)

def iso : (ModuleCat.extendScalars f.appTop.hom).obj ((AffineSectionIs.Construction.AffineSectionAdjunction.sections X).obj M) ≅
    (AffineSectionIs.Construction.AffineSectionAdjunction.sections Y).obj ((Scheme.Modules.pullback f).obj M) :=
  asIso ((AffineSectionIs.Construction.AffineSectionAdjunction.adjunction Y).unit.app _) ≪≫ (AffineSectionIs.Construction.AffineSectionAdjunction.sections Y).mapIso
    (((leftComparison f).app _).symm ≪≫ (Scheme.Modules.pullback f).mapIso (AffineSectionIs.Construction.AffineSectionAdjunction.counitIso X M))

theorem iso_eq_sectionsMap : (iso f M).hom =
    AdjunctionSectionsLeft.Construction.AdjunctionSections.sectionsMap (AffineSectionIs.Construction.AffineSectionAdjunction.adjunction X) (AffineSectionIs.Construction.AffineSectionAdjunction.adjunction Y)
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (ModuleCat.extendRestrictScalarsAdj f.appTop.hom) (AffineSectionIs.Construction.AffineSectionAdjunction.pushforwardIso f) M := by
  rw [AdjunctionSectionsLeft.Construction.AdjunctionSections.sectionsMap, Adjunction.homEquiv_unit]
  rfl

theorem normalization : (ModuleCat.extendRestrictScalarsAdj f.appTop.hom).homEquiv _ _ (iso f M).hom =
    (AffineSectionIs.Construction.AffineSectionAdjunction.sections X).map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (AffineSectionIs.Construction.AffineSectionAdjunction.pushforwardIso f).hom.app ((Scheme.Modules.pullback f).obj M) := by
  rw [iso_eq_sectionsMap]
  exact AdjunctionSectionsLeft.Construction.AdjunctionSections.normalization _ _ _ _ _ M

theorem one_tmul (s : (AffineSectionIs.Construction.AffineSectionAdjunction.sections X).obj M) :
    (iso f M).hom ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, ⊤),f.appTop.hom] s) =
      PullbackSectionRestrict.Construction.PullbackSectionCoefficients.map f M ⊤ s :=
  ConcreteCategory.congr_hom (normalization f M) s

theorem tensorMap_eq_iso : PullbackSectionTensor.Construction.PullbackSectionCoefficients.tensorMap f M ⊤ = (iso f M).hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro s
  exact (PullbackSectionTensor.Construction.PullbackSectionCoefficients.tensorMap_one_tmul f M ⊤ s).trans (one_tmul f M s).symm

theorem tensorMap_isIso : IsIso (PullbackSectionTensor.Construction.PullbackSectionCoefficients.tensorMap f M ⊤) := by
  rw [tensorMap_eq_iso]
  infer_instance

end Construction.AffineGeometricSections

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineGeometric
