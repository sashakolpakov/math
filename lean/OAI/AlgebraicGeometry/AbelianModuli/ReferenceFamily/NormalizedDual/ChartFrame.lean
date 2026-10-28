import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReducedFrame
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NormalizedLocalFrames

/-! # Chart Frame -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ChartFrame

noncomputable section

/-! The constructed normalized local frame pulls back to the actual
restriction of the prescribed global frame on the reduced scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

theorem prescribedReducedLocalFrame_chart (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    {M : (LieRanks.dualNumberTest ℂ ⊗ X).left.Modules}
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)
    (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme)
    (he : Isogenies.NeighborCounting.FramedHom.pullbackFrame (DualOpen.Product.dualOpenReduction X U) e = Dual.NormalizedLocalFrames.prescribedReducedLocalFrame X e₀ U) :
    RepresentationTheory.Theta.Geometric.OpenFramesFactored.pullbackChartFrame (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left M U
      e =
        Isogenies.NeighborCounting.FramedHom.pullbackFrame ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).ι e₀ :=
  ReducedFrame.reducedOpenFrame_chart (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left e₀ U e he

theorem normalizedDualLocalFrame_chart (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    {M : (LieRanks.dualNumberTest ℂ ⊗ X).left.Modules}
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)
    (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme) :
    RepresentationTheory.Theta.Geometric.OpenFramesFactored.pullbackChartFrame (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left M U
      (Dual.NormalizedLocalFrames.normalizedDualLocalFrame X e₀ U e) =
        Isogenies.NeighborCounting.FramedHom.pullbackFrame ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).ι e₀ :=
  prescribedReducedLocalFrame_chart X e₀ U _ (Dual.NormalizedLocalFrames.normalizedDualLocalFrame_reduces X e₀ U e)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.ChartFrame
