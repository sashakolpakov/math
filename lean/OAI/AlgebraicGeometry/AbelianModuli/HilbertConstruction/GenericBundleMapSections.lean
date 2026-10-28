import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegralLineBundleRestrictions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.LocalLinearFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsFunctor

/-! # Generic Bundle Map Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A line-bundle map invertible on a nonempty open of an integral scheme induces an injection on actual global sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsIntegral X] (L M : Line.Bundles.LineBundle X)

theorem Line.Bundles.LineBundle.mapGlobalSections_injective (φ : L.sheaf ⟶ M.sheaf)
    (U : X.Opens) [Nonempty U] [IsIso ((Scheme.Modules.pullback U.ι).map φ)] :
    Function.Injective (φ.app ⊤) := by
  intro s t hst
  apply L.restriction_injective (show U ≤ ⊤ from le_top)
  have hU : U ≤ U.ι.opensRange := by rw [U.opensRange_ι]
  apply (OpenPullback.FrameEquivalence.openPullbackModuleEquiv U.ι (asIso ((Scheme.Modules.pullback U.ι).map φ)) U hU).injective
  rw [Section.LocalLinearFrames.openPullbackModuleEquiv_global_apply, Section.LocalLinearFrames.openPullbackModuleEquiv_global_apply]
  exact (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality U.leTop.op) s).trans
    ((congrArg (M.sheaf.presheaf.map U.leTop.op) hst).trans
      (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality U.leTop.op) t).symm)

theorem Line.Bundles.LineBundle.mapCoefficientSections_injective {R : Type u} [CommRing R]
    (p : X ⟶ Spec (.of R)) (φ : L.sheaf ⟶ M.sheaf)
    (U : X.Opens) [Nonempty U] [IsIso ((Scheme.Modules.pullback U.ι).map φ)] :
    Function.Injective ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).map φ) :=
  L.mapGlobalSections_injective M φ U

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
