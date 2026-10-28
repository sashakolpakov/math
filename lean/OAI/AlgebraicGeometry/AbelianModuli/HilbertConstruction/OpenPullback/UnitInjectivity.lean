import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegralLineBundleRestrictions

/-! # Unit Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Restriction to a nonempty open of an integral scheme makes the canonical line-bundle pullback unit injective on global sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Line.Bundles.LineBundle.openPullbackUnit_top_injective {X : Scheme.{u}} [IsIntegral X]
    (L : Line.Bundles.LineBundle X) (U : X.Opens) [Nonempty U] :
    Function.Injective (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app L.sheaf).app ⊤) := by
  let η := (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app L.sheaf
  have hu : U ≤ U.ι.opensRange := by rw [U.opensRange_ι]
  have : IsIso (η.app U) := OpenPullback.ModuleValues.openPullbackUnit_app_isIso U.ι L.sheaf U hu
  intro s t hst
  apply L.restriction_injective (show U ≤ ⊤ from le_top)
  apply (ConcreteCategory.bijective_of_isIso (η.app U)).injective
  exact (ConcreteCategory.congr_hom (η.mapPresheaf.naturality U.leTop.op) s).trans
    ((congrArg (fun z => ((Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj L.sheaf)).presheaf.map U.leTop.op z) hst).trans
        (ConcreteCategory.congr_hom (η.mapPresheaf.naturality U.leTop.op) t).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
