import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapValues

/-! # Map Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRecovery

noncomputable section

/-! The ambient values recover the original module map on an open subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}

theorem openModuleMapValue_spec (φ : M.restrict f ⟶ N.restrict f)
    (U : Y.Opens) (hU : U ≤ f.opensRange) (s : Γ(M, U)) :
    ((Scheme.Modules.restrictAdjunction f).unit.app N).app U (MapValues.openModuleMapValue f φ U hU s) =
      ((Scheme.Modules.restrictAdjunction f).unit.app M ≫ (Scheme.Modules.pushforward f).map φ).app U s := by
  let := MapValues.moduleRestrictionUnit_app_isIso f N U hU
  exact Module.MapLocalFactor.moduleMapLocalFactor_spec _ _ U s

theorem openModuleMapValue_injective (φ ψ : M.restrict f ⟶ N.restrict f)
    (h : ∀ (U : Y.Opens) (hU : U ≤ f.opensRange),
      MapValues.openModuleMapValue f φ U hU = MapValues.openModuleMapValue f ψ U hU) : φ = ψ := by
  apply Scheme.Modules.hom_ext
  intro W
  let U := f ''ᵁ W
  have hU : U ≤ f.opensRange := f.image_le_opensRange W
  let : IsIso (((Scheme.Modules.restrictAdjunction f).unit.app M).app U) :=
    MapValues.moduleRestrictionUnit_app_isIso f M U hU
  have hα :
      ((Scheme.Modules.restrictAdjunction f).unit.app M ≫ (Scheme.Modules.pushforward f).map φ).app U =
      ((Scheme.Modules.restrictAdjunction f).unit.app M ≫ (Scheme.Modules.pushforward f).map ψ).app U := by
    apply ConcreteCategory.hom_ext
    intro s
    exact (openModuleMapValue_spec f φ U hU s).symm.trans
      ((congrArg (fun z => ((Scheme.Modules.restrictAdjunction f).unit.app N).app U z)
        (LinearMap.congr_fun (h U hU) s)).trans (openModuleMapValue_spec f ψ U hU s))
  change ((Scheme.Modules.restrictAdjunction f).unit.app M).app U ≫ φ.app (f ⁻¹ᵁ U) =
    ((Scheme.Modules.restrictAdjunction f).unit.app M).app U ≫ ψ.app (f ⁻¹ᵁ U) at hα
  have hh := (cancel_epi (((Scheme.Modules.restrictAdjunction f).unit.app M).app U)).mp hα
  exact (congrArg (fun V : X.Opens => φ.app V = ψ.app V) (f.preimage_image_eq W)).mp hh

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRecovery
