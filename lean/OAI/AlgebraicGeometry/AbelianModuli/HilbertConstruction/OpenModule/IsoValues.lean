import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapValues

/-! # Iso Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.IsoValues

noncomputable section

/-! An actual module isomorphism on an open subscheme induces linear equivalences of sections on every smaller ambient open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}

theorem openModuleMapValue_bijective (e : M.restrict f ≅ N.restrict f)
    (U : Y.Opens) (hU : U ≤ f.opensRange) :
    Function.Bijective (MapValues.openModuleMapValue f e.hom U hU) := by
  have := MapValues.moduleRestrictionUnit_app_isIso f M U hU
  have := MapValues.moduleRestrictionUnit_app_isIso f N U hU
  let α := (Scheme.Modules.restrictAdjunction f).unit.app M ≫
    (Scheme.Modules.pushforward f).map e.hom
  have : IsIso (α.app U) := by
    change IsIso (((Scheme.Modules.restrictAdjunction f).unit.app M).app U ≫
      ((Scheme.Modules.pushforward f).map e.hom).app U)
    infer_instance
  exact (Module.MapLocalFactor.moduleMapAppEquiv ((Scheme.Modules.restrictAdjunction f).unit.app N) U).symm.bijective.comp
    (ConcreteCategory.bijective_of_isIso (α.app U))

def openModuleIsoValue (e : M.restrict f ≅ N.restrict f)
    (U : Y.Opens) (hU : U ≤ f.opensRange) : Γ(M, U) ≃ₗ[Γ(Y, U)] Γ(N, U) :=
  LinearEquiv.ofBijective (MapValues.openModuleMapValue f e.hom U hU) (openModuleMapValue_bijective f e U hU)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.IsoValues
