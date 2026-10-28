import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresheafLocalizedRestriction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionMap

/-! # Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.Localization

noncomputable section

/-! Localization of the canonical open-pullback section map is localization of the ordinary restriction map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R]
variable (c : R →+* Γ(X, ⊤)) (M : X.Modules) (V : X.Opens)

theorem coefficientOpenPullbackUnit_isIso_on_open :
    IsIso ((Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap V.ι c M).app (.op V)) := by
  have : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app M).app V) :=
    ModuleValues.openPullbackUnit_app_isIso V.ι M V (by rw [Scheme.Opens.opensRange_ι])
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app M).app V)

theorem coefficientOpenPullback_targetRestriction_isIso :
    IsIso ((Coefficient.ModulePresheaf.coefficientModulePresheaf c
      ((Scheme.Modules.pushforward V.ι).obj ((Scheme.Modules.pullback V.ι).obj M))).map V.leTop.op) := by
  let j := ((TopologicalSpace.Opens.map V.ι.base).map V.leTop).op
  have : IsIso ((TopologicalSpace.Opens.map V.ι.base).map V.leTop) := by
    change IsIso (homOfLE (show V.ι ⁻¹ᵁ V ≤ V.ι ⁻¹ᵁ ⊤ from V.ι.preimage_mono le_top))
    exact homOfLE_isIso_of_eq _ V.ι_preimage_self
  have : IsIso j := inferInstance
  have : IsIso (((Scheme.Modules.pullback V.ι).obj M).presheaf.map j) := inferInstance
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso (((Scheme.Modules.pullback V.ι).obj M).presheaf.map j)

theorem openPullback_localization_implies_restriction (T : Submonoid R)
    [IsLocalizedModule T ((Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap V.ι c M).app (.op ⊤)).hom] :
    IsLocalizedModule T ((Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map V.leTop.op).hom := by
  have := coefficientOpenPullbackUnit_isIso_on_open c M V
  have := coefficientOpenPullback_targetRestriction_isIso c M V
  exact PresheafLocalizedRestriction.presheafRestriction_isLocalized_of_comparison T
    (Coefficient.PullbackSectionMap.coefficientPullbackSectionPresheafMap V.ι c M) V.leTop.op

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.Localization
