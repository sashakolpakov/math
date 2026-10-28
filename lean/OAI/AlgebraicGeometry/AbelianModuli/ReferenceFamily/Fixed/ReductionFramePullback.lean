import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.SquareComposition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.SquareCongruence
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualLine.KernelScalarPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReducedOpenFrameConverse
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReducedFrame

/-! # Reduction Frame Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Fixed.ReductionFramePullback

noncomputable section

/-! Pulling a normalized frame through a map fixing the reduction
preserves the prescribed frame through the actual pullback comparisons. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

theorem fixedReductionFrame_square_normalized {X Y : Scheme.{0}}
    (r : X ⟶ Y) (q : Y ⟶ Y) (hq : r ≫ q = r) (U : Y.Opens)
    (qU : U.toScheme ⟶ U.toScheme) (hU : qU ≫ U.ι = U.ι ≫ q)
    (hrU : (r ∣_ U) ≫ qU = r ∣_ U) {M : Y.Modules}
    (e₀ : (Scheme.Modules.pullback r).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (he : Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) e = ReducedFrame.reducedOpenFrame r e₀ U) :
    Isogenies.NeighborCounting.FramedHom.pullbackFrame (r ∣_ U) (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame q U.ι U.ι qU hU M e) =
      ReducedFrame.reducedOpenFrame r (DualLine.KernelScalarPullback.fixedReductionPullbackFrame r q hq e₀) U := by
  apply ReducedOpenFrameConverse.reducedOpenFrame_of_chart r (DualLine.KernelScalarPullback.fixedReductionPullbackFrame r q hq e₀) U _
  have h₃ : ((r ∣_ U) ≫ qU) ≫ U.ι = (r ⁻¹ᵁ U).ι ≫ (r ≫ q) := by
    rw [Category.assoc, hU, ← Category.assoc, morphismRestrict_ι, Category.assoc]
  have h₁ := Pullback.SquareComposition.pullbackSquareFrame_horizontal r q (r ⁻¹ᵁ U).ι U.ι U.ι (r ∣_ U) qU
    (morphismRestrict_ι r U) hU h₃ M e
  let A := (Scheme.Modules.pullback (r ⁻¹ᵁ U).ι).mapIso ((Scheme.Modules.pullbackComp r q).app M)
  let B := (Scheme.Modules.pullback (r ⁻¹ᵁ U).ι).mapIso ((Scheme.Modules.pullbackCongr hq).app M)
  have h₂ := congrArg (fun f => A ≪≫ f)
    (Pullback.SquareCongruence.pullbackSquareFrame_congr hq (r ⁻¹ᵁ U).ι U.ι hrU h₃ (morphismRestrict_ι r U) M e)
  have h₄ := congrArg (fun f => A ≪≫ B ≪≫ f) (ReducedFrame.reducedOpenFrame_chart r e₀ U e he)
  have h₅ := ReducedFrame.pullbackFrame_precomp (r ⁻¹ᵁ U).ι ((Scheme.Modules.pullbackComp r q).app M)
    ((Scheme.Modules.pullbackCongr hq).app M ≪≫ e₀)
  have h₆ := congrArg (fun f => A ≪≫ f)
    (ReducedFrame.pullbackFrame_precomp (r ⁻¹ᵁ U).ι ((Scheme.Modules.pullbackCongr hq).app M) e₀)
  exact h₁.trans (h₂.trans (h₄.trans (h₅.trans h₆).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Fixed.ReductionFramePullback
