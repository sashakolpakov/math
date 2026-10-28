import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CechMorphismCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RestrictedSquareFrameTransitions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameDualCech

/-! # Frame Cech Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.FrameCechMorphism

noncomputable section

/-! First-order coefficients of actual pulled frame transitions
are the original reduced section pullbacks, on the refined Cech cover. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ Y).left))]
    (f : X ⟶ Y) (M : (LieRanks.dualNumberTest ℂ ⊗ Y).left.Modules) {I J : Type}
    (U : I → (LieRanks.dualNumberTest ℂ ⊗ Y).left.Opens) (V : J → (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens)
    (r : J → I) (h : ∀ j, V j ≤ (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left ⁻¹ᵁ U (r j))
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (e : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule (U i).toScheme)

theorem lineFrameDualCech_morphism (a : Fin 2 → J) :
    (LineFrameDualCech.lineFrameDualCech X (fun j => TensorCechCoefficients.localFrameFromPullback (V j)
      (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left (V j).ι (U (r j)).ι
        ((𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left.resLE (U (r j)) (V j) (h j))
        (Scheme.Hom.resLE_comp_ι _ (h j)) M (e (r j)))) hV a).val.snd =
      f.left.appLE (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (CechCoefficient.dualReducedCechCover Y U) (r ∘ a))
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (CechCoefficient.dualReducedCechCover X V) a)
        (StructureCechRefinedPullback.cechMorphismIntersection_le f.left (CechCoefficient.dualReducedCechCover Y U) (CechCoefficient.dualReducedCechCover X V) r
          (fun j => MorphismOpenReductionSquare.dualMorphismReducedOpen_le f (U (r j)) (V j) (h j)) a)
        (show Γ(Y.left, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (CechCoefficient.dualReducedCechCover Y U) (r ∘ a)) from
          (LineFrameDualCech.lineFrameDualCech Y (fun i => TensorCechCoefficients.localFrameFromPullback (U i) (e i)) hU (r ∘ a)).val.snd) := by
  have ht := RestrictedSquareFrameTransitions.restrictedSquareFrame_transition (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left M
    (U (r (a 0))) (U (r (a 1))) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (r ∘ a))
    (V (a 0)) (V (a 1)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection V a)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U (r ∘ a) 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U (r ∘ a) 1)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le V a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le V a 1)
    (h (a 0)) (h (a 1)) (StructureCechRefinedPullback.cechMorphismIntersection_le (𝟙 (LieRanks.dualNumberTest ℂ) ⊗ₘ f).left U V r h a)
    (e (r (a 0))) (e (r (a 1)))
  have h₁ := congrArg (fun u => (Units.map (CechCoefficient.dualCechSectionCoefficientEquiv X V hV a).toMonoidHom u).val.snd) ht
  let u := (TensorCechCoefficients.localFrameFromPullback (U (r (a 0))) (e (r (a 0)))).transition
    (TensorCechCoefficients.localFrameFromPullback (U (r (a 1))) (e (r (a 1))))
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U (r ∘ a)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U (r ∘ a) 0)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U (r ∘ a) 1)
  have h₂ := congrArg TrivSqZeroExt.snd
    (CechMorphismCoefficients.dualCechSectionCoefficientEquiv_morphism f U V r h hU hV a u.val)
  exact h₁.trans h₂

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.FrameCechMorphism
