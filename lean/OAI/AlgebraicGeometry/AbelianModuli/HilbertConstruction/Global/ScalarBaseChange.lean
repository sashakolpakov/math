import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleScalars

/-! # Scalar Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarBaseChange

noncomputable section

/-! The action of a global regular function commutes with pushforward and pullback of module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem globalFunction_pullback_restrict (f : X ⟶ Y) (r : Γ(Y, ⊤)) (U : Y.Opens) :
    X.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op (f.appTop r) =
      f.app U (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) :=
  (ConcreteCategory.congr_hom (f.naturality (homOfLE (show U ≤ ⊤ from le_top)).op) r).symm

theorem globalModuleScalar_pushforward (f : X ⟶ Y) (M : X.Modules) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.pushforward f).map (ModuleScalars.globalModuleScalar M (f.appTop r)) =
      ModuleScalars.globalModuleScalar ((Scheme.Modules.pushforward f).obj M) r := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro m
  change Γ(M, f ⁻¹ᵁ U) at m
  change X.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op (f.appTop r) • m =
    f.app U (Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) • m
  rw [globalFunction_pullback_restrict]

theorem globalModuleScalar_pullback (f : X ⟶ Y) (M : Y.Modules) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).map (ModuleScalars.globalModuleScalar M r) =
      ModuleScalars.globalModuleScalar ((Scheme.Modules.pullback f).obj M) (f.appTop r) := by
  let u := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M
  have hn : ModuleScalars.globalModuleScalar M r ≫ u = u ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map (ModuleScalars.globalModuleScalar M r)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality (ModuleScalars.globalModuleScalar M r)
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv M
    ((Scheme.Modules.pullback f).obj M)).injective
  change u ≫ (Scheme.Modules.pushforward f).map ((Scheme.Modules.pullback f).map
    (ModuleScalars.globalModuleScalar M r)) = u ≫ (Scheme.Modules.pushforward f).map
      (ModuleScalars.globalModuleScalar ((Scheme.Modules.pullback f).obj M) (f.appTop r))
  exact hn.symm.trans ((ModuleScalars.globalModuleScalar_natural r u).trans
    (congrArg (fun a => u ≫ a)
      (globalModuleScalar_pushforward f ((Scheme.Modules.pullback f).obj M) r).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarBaseChange
