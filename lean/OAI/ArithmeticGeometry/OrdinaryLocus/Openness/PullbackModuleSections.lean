import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit

/-! # Pullback Module Sections -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackModuleSections.Construction

noncomputable section

/-! The canonical pullback of module sections, with scalar and functorial compatibility. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def modulePullbackGlobalSection (M : Y.Modules) :
    Γ(M, ⊤) →+ Γ((Scheme.Modules.pullback f).obj M, ⊤) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤).hom

theorem modulePullbackGlobalSection_smul (M : Y.Modules) (r : Γ(Y, ⊤)) (m : Γ(M, ⊤)) :
    modulePullbackGlobalSection f M (r • m) =
      f.appTop r • modulePullbackGlobalSection f M m :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app_smul r m

theorem modulePullbackGlobalSection_naturality {M N : Y.Modules} (φ : M ⟶ N) (m : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback f).map φ).app ⊤ (modulePullbackGlobalSection f M m) =
      modulePullbackGlobalSection f N (φ.app ⊤ m) :=
  (congrArg (fun q : M ⟶ (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj N) ↦
    q.app ⊤ m) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ)).symm

theorem modulePullbackGlobalSection_unit (r : Γ(Y, ⊤)) :
    (LineBundle.Construction.pullbackStructureSheafIso f).hom.app ⊤
      (modulePullbackGlobalSection f (LineBundle.Construction.structureSheafModule Y) r) = f.appTop r :=
  congrArg (fun q : LineBundle.Construction.structureSheafModule Y ⟶
    (Scheme.Modules.pushforward f).obj (LineBundle.Construction.structureSheafModule X) ↦ q.app ⊤ r)
      (TensorUnit.Construction.pullbackStructureSheafIso_unit f)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackModuleSections.Construction
