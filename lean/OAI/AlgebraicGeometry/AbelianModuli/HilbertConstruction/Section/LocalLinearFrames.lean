import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenPullback.FrameEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.EndRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames

/-! # Local Linear Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.LocalLinearFrames

noncomputable section

/-! A global section gives an actual linear frame on every open contained in its nonvanishing locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

theorem openPullbackModuleEquiv_global_apply (f : X ⟶ Y) [IsOpenImmersion f]
    {M N : Y.Modules} (φ : M ⟶ N) [IsIso ((Scheme.Modules.pullback f).map φ)]
    (V : Y.Opens) (hV : V ≤ f.opensRange) (x : Γ(M, V)) :
    OpenPullback.FrameEquivalence.openPullbackModuleEquiv f (asIso ((Scheme.Modules.pullback f).map φ)) V hV x = φ.app V x := by
  have h₁ := OpenPullback.ModuleValues.openPullbackModuleValue_restriction f ((Scheme.Modules.pullback f).map φ) V hV
  have h₂ := congrArg (fun a => OpenModule.MapValues.openModuleMapValue f a V hV) (LineBundle.EndRecovery.pullbackModuleRestrictionMap_global f φ)
  have h₃ := OpenModule.MapValues.openModuleMapValue_from_global f φ V hV
  exact LinearMap.congr_fun (h₁.symm.trans (h₂.trans h₃)) x

def sectionLocalFrameEquiv {M : X.Modules} (s : Line.Bundles.structureModule X ⟶ M)
    (V : X.Opens) (hV : V ≤ Ample.LineBundles.sectionNonvanishing s) : Γ(X, V) ≃ₗ[Γ(X, V)] Γ(M, V) := by
  have : IsIso ((Scheme.Modules.pullback (Ample.LineBundles.sectionNonvanishing s).ι).map s) :=
    (Nonvanishing.isIso_pullbackSection_iff (Ample.LineBundles.sectionNonvanishing s).ι s).mp inferInstance
  exact OpenPullback.FrameEquivalence.openPullbackModuleEquiv (Ample.LineBundles.sectionNonvanishing s).ι
    (asIso ((Scheme.Modules.pullback (Ample.LineBundles.sectionNonvanishing s).ι).map s)) V
      (by simpa only [(Ample.LineBundles.sectionNonvanishing s).opensRange_ι] using hV)

theorem sectionLocalFrameEquiv_apply {M : X.Modules} (s : Line.Bundles.structureModule X ⟶ M)
    (V : X.Opens) (hV : V ≤ Ample.LineBundles.sectionNonvanishing s) (r : Γ(X, V)) :
    sectionLocalFrameEquiv s V hV r = s.app V r := by
  have : IsIso ((Scheme.Modules.pullback (Ample.LineBundles.sectionNonvanishing s).ι).map s) :=
    (Nonvanishing.isIso_pullbackSection_iff (Ample.LineBundles.sectionNonvanishing s).ι s).mp inferInstance
  exact openPullbackModuleEquiv_global_apply (Ample.LineBundles.sectionNonvanishing s).ι s V
    (by simpa only [(Ample.LineBundles.sectionNonvanishing s).opensRange_ι] using hV) r

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.LocalLinearFrames
