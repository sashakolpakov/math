import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReducedOpenFrameConverse
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Global.FrameOverComparison

/-! # Open Frame Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.OpenFrameCriterion

noncomputable section

/-! Native open-frame normalization implies the exact normalization
condition on the corresponding pullback frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

theorem reducedOpenFrame_of_open {X Y : Scheme.{0}} (r : X ⟶ Y) {M : Y.Modules}
    (e₀ : (Scheme.Modules.pullback r).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X) (U : Y.Opens)
    (e : M.restrict U.ι ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (h : RepresentationTheory.Theta.Geometric.Pullback.Algebraic.pullbackOpenFrame r M U e = Global.FrameOverComparison.globalOpenFrame e₀ (r ⁻¹ᵁ U)) :
    Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e) =
      ReducedFrame.reducedOpenFrame r e₀ U := by
  apply ReducedOpenFrameConverse.reducedOpenFrame_of_chart r e₀ U _
  have h₁ := RepresentationTheory.Theta.Geometric.OpenFramesFactored.pullbackOpenFrame_as_chart r M U e
  have h₂ := congrArg (fun q => (Scheme.Modules.restrictFunctorIsoPullback (r ⁻¹ᵁ U).ι).symm.app
    ((Scheme.Modules.pullback r).obj M) ≪≫ q) h
  exact h₁.symm.trans (h₂.trans ((Global.FrameOverComparison.globalOpenFrame_pullback e₀ (r ⁻¹ᵁ U)).trans
    (ReducedFrame.nativePullbackFrame_agrees (r ⁻¹ᵁ U).ι e₀)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Normalized.OpenFrameCriterion
