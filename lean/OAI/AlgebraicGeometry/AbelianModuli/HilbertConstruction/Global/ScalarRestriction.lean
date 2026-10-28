import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarBaseChange

/-! # Scalar Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarRestriction

noncomputable section

/-! Restriction along an open immersion respects multiplication by a global function. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem globalModuleScalar_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.restrictFunctor f).map (ModuleScalars.globalModuleScalar M r) =
      ModuleScalars.globalModuleScalar (M.restrict f) (f.appTop r) := by
  let e := (Scheme.Modules.restrictFunctorIsoPullback f).app M
  apply (cancel_mono e.hom).mp
  calc
    _ = e.hom ≫ (Scheme.Modules.pullback f).map (ModuleScalars.globalModuleScalar M r) :=
      (Scheme.Modules.restrictFunctorIsoPullback f).hom.naturality (ModuleScalars.globalModuleScalar M r)
    _ = e.hom ≫ ModuleScalars.globalModuleScalar ((Scheme.Modules.pullback f).obj M) (f.appTop r) := by
      rw [ScalarBaseChange.globalModuleScalar_pullback]
    _ = _ := (ModuleScalars.globalModuleScalar_natural (f.appTop r) e.hom).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarRestriction
