import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.Product
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SplitFrameReduction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames

/-! # Normalized Local Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NormalizedLocalFrames

noncomputable section

/-! Every actual line bundle with a frame on its reduced fiber has
affine local frames lifting that prescribed reduced frame exactly. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FramedHom

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) {M : (LieRanks.dualNumberTest ℂ ⊗ X).left.Modules}
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj M ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left) (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)

def prescribedReducedLocalFrame :
    (Scheme.Modules.pullback (DualOpen.Product.dualOpenReduction X U)).obj
      ((Scheme.Modules.pullback U.ι).obj M) ≅
        ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).toScheme :=
  (Scheme.Modules.pullbackComp (DualOpen.Product.dualOpenReduction X U) U.ι).app M ≪≫
    (Scheme.Modules.pullbackCongr (DualOpen.Product.dualOpenReduction_ι X U)).app M ≪≫
    (Scheme.Modules.pullbackComp ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).ι
      (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).symm.app M ≪≫
    Isogenies.NeighborCounting.FramedHom.pullbackFrame ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ U).ι e₀

def normalizedDualLocalFrame
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme) :
    (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme :=
  SplitFrameReduction.splitReductionFrameLift (DualOpen.Product.dualOpenReduction X U) (DualOpen.Product.dualOpenProjection X U) e
    (prescribedReducedLocalFrame X e₀ U)

theorem normalizedDualLocalFrame_reduces
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme) :
    Isogenies.NeighborCounting.FramedHom.pullbackFrame (DualOpen.Product.dualOpenReduction X U) (normalizedDualLocalFrame X e₀ U e) =
      prescribedReducedLocalFrame X e₀ U :=
  SplitFrameReduction.splitReductionFrameLift_reduces (DualOpen.Product.dualOpenReduction X U) (DualOpen.Product.dualOpenProjection X U)
    (DualOpen.Product.dualOpenReduction_projection X U) e (prescribedReducedLocalFrame X e₀ U)

theorem exists_affine_normalized_dual_frame
    (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (eL : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left) (x : X.left) :
    ∃ W : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens,
      x ∈ (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ W ∧ IsAffineOpen W ∧
      IsAffineOpen ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left ⁻¹ᵁ W) ∧
      ∃ e : (Scheme.Modules.pullback W.ι).obj L.sheaf ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule W.toScheme,
        Isogenies.NeighborCounting.FramedHom.pullbackFrame (DualOpen.Product.dualOpenReduction X W) e = prescribedReducedLocalFrame X eL W := by
  obtain ⟨W, hx, hW, ⟨e⟩⟩ := L.exists_affine_frame ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left x)
  exact ⟨W, hx, hW, ReductionOpens.dualAffineOpen_reduction X W hW, normalizedDualLocalFrame X eL W e,
    normalizedDualLocalFrame_reduces X eL W e⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NormalizedLocalFrames
