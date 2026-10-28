import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.RefinementNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapSlicePullback

/-! # Map Refinement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRefinement

noncomputable section

/-! Ambient values of module maps are unchanged under refinement of open subsets. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem openPullbackModuleValue_congr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) {M N : Y.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (U : Y.Opens) (hf : U ≤ f.opensRange) (hg : U ≤ g.opensRange) :
    OpenPullback.ModuleValues.openPullbackModuleValue g (Module.MapPullbackCongruence.moduleMapPullbackCongr h φ) U hg =
      OpenPullback.ModuleValues.openPullbackModuleValue f φ U hf := by
  subst g
  rfl

def openSubsetOver {X : Scheme.{u}} (U : X.Opens) : Over X := Over.mk U.ι

def openSubsetOverMap {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) :
    openSubsetOver U ⟶ openSubsetOver V := Over.homMk (X.homOfLE h) (X.homOfLE_ι h)

theorem openPullbackModuleValue_refine {X : Scheme.{u}} {M N : X.Modules}
    {U V : X.Opens} (h : U ≤ V)
    (φ : (Scheme.Modules.pullback V.ι).obj M ⟶ (Scheme.Modules.pullback V.ι).obj N) :
    OpenPullback.ModuleValues.openPullbackModuleValue U.ι (Module.MapSlicePullback.moduleMapPullbackAlong (openSubsetOverMap h) φ) U
        (by rw [U.opensRange_ι]) =
      OpenPullback.ModuleValues.openPullbackModuleValue V.ι φ U (by rwa [V.opensRange_ι]) := by
  have hc : U ≤ (X.homOfLE h ≫ V.ι).opensRange := by
    intro x hx
    change ∃ y : U.toScheme, (X.homOfLE h ≫ V.ι) y = x
    exact ⟨⟨x, hx⟩, congrArg (fun k : U.toScheme ⟶ X => k ⟨x, hx⟩) (X.homOfLE_ι h)⟩
  exact (openPullbackModuleValue_congr (X.homOfLE_ι h)
    (Module.MapPullbackComposition.moduleMapPullbackComp (X.homOfLE h) V.ι φ) U hc _).trans
      (OpenPullback.RefinementNaturality.openPullbackModuleValue_comp (X.homOfLE h) V.ι φ U hc)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRefinement
