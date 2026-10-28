import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReducedFrame
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NormalizedFrameCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameIsoTransport

/-! # Frame Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Actual module isomorphisms transport normalized affine frames
and the prescribed global reduction frame compatibly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (L K : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left) (q : K.sheaf ≅ L.sheaf)

def Dual.NormalizedFrameCover.NormalizedDualFrame.precomp (a : Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀) :
    Dual.NormalizedFrameCover.NormalizedDualFrame X K ((Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).mapIso q ≪≫ e₀) where
  domain := a.domain
  affine := a.affine
  frame := (Scheme.Modules.pullback a.domain.ι).mapIso q ≪≫ a.frame
  reduces := by
    have h₁ := ReducedFrame.pullbackFrame_precomp (DualOpen.Product.dualOpenReduction X a.domain)
      ((Scheme.Modules.pullback a.domain.ι).mapIso q) a.frame
    have h₂ := congrArg (fun e => (Scheme.Modules.pullback (DualOpen.Product.dualOpenReduction X a.domain)).mapIso
      ((Scheme.Modules.pullback a.domain.ι).mapIso q) ≪≫ e) a.reduces
    exact h₁.trans (h₂.trans (ReducedFrame.reducedOpenFrame_precomp (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left q e₀ a.domain).symm)

theorem Dual.NormalizedFrameCover.NormalizedDualFrame.precomp_localFrame (a : Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀) :
    (a.precomp X L K e₀ q).localFrame X K
      ((Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).mapIso q ≪≫ e₀) =
        (a.localFrame X L e₀).precomp q := by
  have h := ReducedFrame.transportedFrame_precomp (Scheme.Modules.restrictFunctorIsoPullback a.domain.ι) q a.frame
  exact congrArg (fun e => (⟨a.domain, e⟩ : LineFrameAtlas.LocalLineFrame K.sheaf)) h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
