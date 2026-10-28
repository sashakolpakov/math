import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PushforwardModuleComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PullbackSectionMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues

/-! # Open Pullback Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.OpenPullbackValues

noncomputable section

/-! Restriction to an open subscheme preserves coefficient-module sections on every open contained in its image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]
variable (a : Y ⟶ X) [IsOpenImmersion a] (f : R →+* Γ(X, ⊤)) (M : X.Modules)

theorem coefficientOpenPullbackUnit_isIso (U : X.Opens) (hU : U ≤ a.opensRange) :
    IsIso ((PullbackSectionMap.coefficientPullbackSectionPresheafMap a f M).app (.op U)) := by
  have hu := OpenPullback.ModuleValues.openPullbackUnit_app_isIso a M U hU
  have hb := (ConcreteCategory.isIso_iff_bijective
    (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app U)).mp hu
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hb

def coefficientOpenPullbackValueIso (U : X.Opens) (hU : U ≤ a.opensRange) :
    (ModulePresheaf.coefficientModulePresheaf f M).obj (.op U) ≅
      (ModulePresheaf.coefficientModulePresheaf (a.appTop.hom.comp f) ((Scheme.Modules.pullback a).obj M)).obj (.op (a ⁻¹ᵁ U)) := by
  have := coefficientOpenPullbackUnit_isIso a f M U hU
  exact asIso ((PullbackSectionMap.coefficientPullbackSectionPresheafMap a f M).app (.op U)) ≪≫
    (PushforwardModuleComparison.coefficientPushforwardModuleIso a f ((Scheme.Modules.pullback a).obj M)).app (.op U)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.OpenPullbackValues
