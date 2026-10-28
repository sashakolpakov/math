import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.ModuleValues

/-! # Frame Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.FrameEquivalence

noncomputable section

/-! An isomorphism between pullbacks along an open immersion gives an actual linear equivalence of sections on every contained ambient open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules}

def openPullbackModuleEquiv
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N)
    (V : Y.Opens) (hV : V ≤ f.opensRange) : Γ(M, V) ≃ₗ[Γ(Y, V)] Γ(N, V) := by
  let α := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
    (Scheme.Modules.pushforward f).map e.hom
  let β := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N
  have : IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app V) :=
    ModuleValues.openPullbackUnit_app_isIso f M V hV
  have : IsIso (β.app V) := ModuleValues.openPullbackUnit_app_isIso f N V hV
  have : IsIso (α.app V) := by
    change IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map e.hom).app V)
    rw [Scheme.Modules.Hom.comp_app]
    infer_instance
  exact (Module.MapLocalFactor.moduleMapAppEquiv α V).trans (Module.MapLocalFactor.moduleMapAppEquiv β V).symm

theorem openPullbackModuleEquiv_apply
    (e : (Scheme.Modules.pullback f).obj M ≅ (Scheme.Modules.pullback f).obj N)
    (V : Y.Opens) (hV : V ≤ f.opensRange) (x : Γ(M, V)) :
    openPullbackModuleEquiv f e V hV x = ModuleValues.openPullbackModuleValue f e.hom V hV x := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.FrameEquivalence
