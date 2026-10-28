import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRefinement
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndRecovery

/-! # Map Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.MapGluing

noncomputable section

/-! Compatible maps between canonical module pullbacks glue on an open cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens) (M N : X.Modules)

structure OpenPullbackModuleMaps where
  localMap : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ⟶
    (Scheme.Modules.pullback (U i).ι).obj N
  agree : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
    Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap hi) (localMap i) =
      Module.MapSlicePullback.moduleMapPullbackAlong (OpenModule.MapRefinement.openSubsetOverMap hj) (localMap j)

namespace OpenPullbackModuleMaps

variable {U M N} (D : OpenPullbackModuleMaps U M N)

def restrictionData : Module.OpenMapGluing.OpenCoverModuleMaps U M N where
  localMap i := ModuleValues.pullbackModuleRestrictionMap (U i).ι (D.localMap i)
  agree i j V hi hj := by
    have hi' : V ≤ (U i).ι.opensRange := by rwa [(U i).opensRange_ι]
    have hj' : V ≤ (U j).ι.opensRange := by rwa [(U j).opensRange_ι]
    have hV : V ≤ V.ι.opensRange := by rw [V.opensRange_ι]
    exact (ModuleValues.openPullbackModuleValue_restriction (U i).ι (D.localMap i) V hi').trans
      ((OpenModule.MapRefinement.openPullbackModuleValue_refine hi (D.localMap i)).symm.trans
        ((congrArg (fun φ => ModuleValues.openPullbackModuleValue V.ι φ V hV) (D.agree i j V hi hj)).trans
          ((OpenModule.MapRefinement.openPullbackModuleValue_refine hj (D.localMap j)).trans
            (ModuleValues.openPullbackModuleValue_restriction (U j).ι (D.localMap j) V hj').symm)))

def glue (hU : ∀ x : X, ∃ i, x ∈ U i) : M ⟶ N := D.restrictionData.glue hU

theorem glue_pullback (hU : ∀ x : X, ∃ i, x ∈ U i) (i : ι) :
    (Scheme.Modules.pullback (U i).ι).map (D.glue hU) = D.localMap i := by
  apply LineBundle.EndRecovery.pullbackModuleRestrictionMap_injective (U i).ι M N
  rw [LineBundle.EndRecovery.pullbackModuleRestrictionMap_global]
  exact D.restrictionData.glue_restrict hU i

theorem glue_unique (hU : ∀ x : X, ∃ i, x ∈ U i) (φ : M ⟶ N)
    (hφ : ∀ i, (Scheme.Modules.pullback (U i).ι).map φ = D.localMap i) : φ = D.glue hU := by
  apply Module.MapCoverEquality.moduleMap_eq_of_pullback_cover U hU
  intro i
  exact (hφ i).trans (D.glue_pullback hU i).symm

theorem existsUnique_glue (hU : ∀ x : X, ∃ i, x ∈ U i) :
    ∃! φ : M ⟶ N, ∀ i, (Scheme.Modules.pullback (U i).ι).map φ = D.localMap i :=
  ⟨D.glue hU, D.glue_pullback hU, D.glue_unique hU⟩

end OpenPullbackModuleMaps

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.MapGluing
