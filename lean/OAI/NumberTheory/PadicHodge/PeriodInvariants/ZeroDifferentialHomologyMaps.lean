import OAI.NumberTheory.PadicHodge.PeriodInvariants.ModuleHomologyMaps

/-! # Zero Differential Homology Maps -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ZeroDifferentialHomologyMaps

noncomputable section

/-!
# Maps on homology when there are no incoming boundaries

With zero first differentials, bijectivity on the explicit kernels is
equivalent to a quasi-isomorphism of the actual short complexes.
-/

universe u v

open _root_.CategoryTheory OAI.NumberTheory.PadicHodge.PeriodInvariants.ModuleHomologyMaps

variable {R : Type u} [CommRing R] {S T : ShortComplex (ModuleCat.{v} R)}

theorem quasiIso_iff_cycleMap_bijective (f : S ⟶ T) (hS : S.f = 0) (hT : T.f = 0) :
    ShortComplex.QuasiIso f ↔ Function.Bijective (ModuleHomologyMaps.cycleMap f) := by
  let γ := ShortComplex.LeftHomologyMapData.ofIsLimitKernelFork f
    hS _ S.moduleCatLeftHomologyData.hi hT _ T.moduleCatLeftHomologyData.hi
    (ModuleCat.ofHom (ModuleHomologyMaps.cycleMap f)) rfl
  exact γ.quasiIso_iff.trans (ConcreteCategory.isIso_iff_bijective _)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ZeroDifferentialHomologyMaps
