import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.MapRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.TensorCompositionUnits

/-! # Module Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues

noncomputable section

/-! Ambient section values for local maps between canonical pullbacks of module sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

theorem openPullbackUnit_app_isIso (M : Y.Modules) (U : Y.Opens) (hU : U ≤ f.opensRange) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U) := by
  let : IsIso (((Scheme.Modules.restrictAdjunction f).unit.app M).app U) :=
    OpenModule.MapValues.moduleRestrictionUnit_app_isIso f M U hU
  have h := congrArg (fun ψ : M ⟶ (Scheme.Modules.pushforward f).obj
      ((Scheme.Modules.pullback f).obj M) => ψ.app U)
    ((Scheme.Modules.restrictAdjunction f).unit_leftAdjointUniq_hom_app
      (Scheme.Modules.pullbackPushforwardAdjunction f) M)
  rw [← h, Scheme.Modules.Hom.comp_app]
  infer_instance

variable {M N : Y.Modules}

def pullbackModuleRestrictionMap
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N) :
    M.restrict f ⟶ N.restrict f :=
  (Scheme.Modules.restrictFunctorIsoPullback f).hom.app M ≫ φ ≫
    (Scheme.Modules.restrictFunctorIsoPullback f).inv.app N

def openPullbackModuleValue
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (U : Y.Opens) (hU : U ≤ f.opensRange) : Γ(M, U) →ₗ[Γ(Y, U)] Γ(N, U) := by
  letI := openPullbackUnit_app_isIso f N U hU
  exact Module.MapLocalFactor.moduleMapLocalFactor
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫ (Scheme.Modules.pushforward f).map φ)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) U

theorem openPullbackModuleValue_spec
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (U : Y.Opens) (hU : U ≤ f.opensRange) (s : Γ(M, U)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app U
      (openPullbackModuleValue f φ U hU s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforward f).map φ).app U s := by
  let := openPullbackUnit_app_isIso f N U hU
  exact Module.MapLocalFactor.moduleMapLocalFactor_spec _ _ U s

theorem openPullbackModuleValue_restriction
    (φ : (Scheme.Modules.pullback f).obj M ⟶ (Scheme.Modules.pullback f).obj N)
    (U : Y.Opens) (hU : U ≤ f.opensRange) :
    OpenModule.MapValues.openModuleMapValue f (pullbackModuleRestrictionMap f φ) U hU =
      openPullbackModuleValue f φ U hU := by
  let := openPullbackUnit_app_isIso f N U hU
  have hM : (Scheme.Modules.restrictAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M :=
    (Scheme.Modules.restrictAdjunction f).unit_leftAdjointUniq_hom_app
      (Scheme.Modules.pullbackPushforwardAdjunction f) M
  have hN : (Scheme.Modules.restrictAdjunction f).unit.app N ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app N) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N :=
    (Scheme.Modules.restrictAdjunction f).unit_leftAdjointUniq_hom_app
      (Scheme.Modules.pullbackPushforwardAdjunction f) N
  have hα : ((Scheme.Modules.restrictAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map (pullbackModuleRestrictionMap f φ)) ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app N) =
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
        (Scheme.Modules.pushforward f).map φ := by
    have he : pullbackModuleRestrictionMap f φ ≫
        (Scheme.Modules.restrictFunctorIsoPullback f).hom.app N =
        (Scheme.Modules.restrictFunctorIsoPullback f).hom.app M ≫ φ := by
      simp only [pullbackModuleRestrictionMap, Category.assoc,
        (Scheme.Modules.restrictFunctorIsoPullback f).inv_hom_id_app, Category.comp_id]
    rw [Category.assoc, ← Functor.map_comp, he, Functor.map_comp, ← Category.assoc, hM]
  apply Module.MapLocalFactor.moduleMapLocalFactor_unique
  intro s
  have hNs := congrArg (fun ψ : N ⟶ (Scheme.Modules.pushforward f).obj
    ((Scheme.Modules.pullback f).obj N) => ψ.app U) hN
  rw [← hNs]
  change ((Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app N)).app U
    (((Scheme.Modules.restrictAdjunction f).unit.app N).app U
      (OpenModule.MapValues.openModuleMapValue f (pullbackModuleRestrictionMap f φ) U hU s)) = _
  rw [OpenModule.MapRecovery.openModuleMapValue_spec]
  exact ConcreteCategory.congr_hom (congrArg (fun ψ => ψ.app U) hα) s

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues
