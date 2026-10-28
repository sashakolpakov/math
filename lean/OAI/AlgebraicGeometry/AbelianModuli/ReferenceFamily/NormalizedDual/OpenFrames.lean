import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ChartFrame
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.FrameOverComparison
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NormalizedFrameCover

/-! # Open Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenFrames

noncomputable section

/-! The normalized actual local frames pull back to one prescribed
global reduced frame on all their opens and all smaller common opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)

theorem normalizedDualFrame_open (a : Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀) :
    RepresentationTheory.Theta.Geometric.Pullback.Algebraic.pullbackOpenFrame (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left L.sheaf a.domain
      (a.localFrame X L e₀).frame = Global.FrameOverComparison.globalOpenFrame e₀ (a.baseOpen X L e₀) := by
  have he : (Scheme.Modules.restrictFunctorIsoPullback a.domain.ι).symm.app L.sheaf ≪≫
      (a.localFrame X L e₀).frame = a.frame :=
    Iso.symm_self_id_assoc _ _
  have h := RepresentationTheory.Theta.Geometric.OpenFramesFactored.pullbackOpenFrame_as_chart (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left
    L.sheaf a.domain (a.localFrame X L e₀).frame
  have h' := congrArg (fun q : (Scheme.Modules.pullback a.domain.ι).obj L.sheaf ≅
    ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule a.domain.toScheme =>
      RepresentationTheory.Theta.Geometric.OpenFramesFactored.pullbackChartFrame (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left L.sheaf a.domain q) he
  have hc := ChartFrame.prescribedReducedLocalFrame_chart X e₀ a.domain a.frame a.reduces
  have hg := Global.FrameOverComparison.globalOpenFrame_pullback e₀ (a.baseOpen X L e₀)
  have hg' := ReducedFrame.nativePullbackFrame_agrees (a.baseOpen X L e₀).ι e₀
  let b := (Scheme.Modules.restrictFunctorIsoPullback (a.baseOpen X L e₀).ι).symm.app
    ((Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf)
  apply Iso.ext
  apply (cancel_epi b.hom).mp
  exact congrArg Iso.hom (h.trans (h'.trans (hc.trans (hg.trans hg').symm)))

theorem normalizedDualFrame_open_restrict (a : Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀)
    (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : U ≤ a.domain) :
    RepresentationTheory.Theta.Geometric.Pullback.Algebraic.pullbackOpenFrame (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left L.sheaf U
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hU (a.localFrame X L e₀).frame) =
        Global.FrameOverComparison.globalOpenFrame e₀ ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U) := by
  have h₁ := RepresentationTheory.Theta.Geometric.Pullback.OpenFrameRestriction.pullbackOpenFrame_restrict (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left
    L.sheaf hU (a.localFrame X L e₀).frame
  have h₂ := congrArg (fun q => SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization
    ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.preimage_mono hU) q)
      (normalizedDualFrame_open X L e₀ a)
  exact h₁.symm.trans (h₂.trans (Global.FrameOverComparison.globalOpenFrame_restrict e₀
    ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.preimage_mono hU)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenFrames
