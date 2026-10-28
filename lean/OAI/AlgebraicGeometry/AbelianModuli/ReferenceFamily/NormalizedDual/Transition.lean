import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.OpenFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Open.FrameTransitionPullback
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameCoordinates

/-! # Transition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.Transition

noncomputable section

/-! Actual normalized local frames have transition units whose
restriction to the reduced scheme is one on every common open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem nativeOpenFrameTransition_reduces_one {X Y : Scheme.{0}} (r : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens)
    (e f : M.restrict U.ι ≅ HilbertConstruction.Line.Bundles.structureModule U.toScheme)
    (h : RepresentationTheory.Theta.Geometric.Pullback.Algebraic.pullbackOpenFrame r M U e = RepresentationTheory.Theta.Geometric.Pullback.Algebraic.pullbackOpenFrame r M U f) :
    Units.map (r.app U).hom.toMonoidHom (RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit M U e f) = 1 := by
  refine (Open.FrameTransitionPullback.nativeOpenFrameTransition_pullback r M U e f).trans ?_
  exact (congrArg (fun q => RepresentationTheory.Theta.Geometric.IntrinsicFrame.TransitionUnits.frameTransitionUnit ((Scheme.Modules.pullback r).obj M)
    (r ⁻¹ᵁ U) q (RepresentationTheory.Theta.Geometric.Pullback.Algebraic.pullbackOpenFrame r M U f)) h).trans
      (Open.FrameTransitionPullback.nativeOpenFrameTransition_self _ _ _)

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)

theorem normalizedDualFrame_transition_reduces (a b : Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀)
    (U : (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (ha : U ≤ a.domain) (hb : U ≤ b.domain) :
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.app U
      ((a.localFrame X L e₀).transition (b.localFrame X L e₀) U ha hb).val = 1 := by
  have h₁ := congrArg (Units.map ((RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.app U).hom.toMonoidHom)
    ((a.localFrame X L e₀).transition_native L.sheaf (b.localFrame X L e₀) U ha hb)
  have h₂ := nativeOpenFrameTransition_reduces_one (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left
    L.sheaf U (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization ha (a.localFrame X L e₀).frame)
      (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hb (b.localFrame X L e₀).frame)
      ((OpenFrames.normalizedDualFrame_open_restrict X L e₀ a U ha).trans
        (OpenFrames.normalizedDualFrame_open_restrict X L e₀ b U hb).symm)
  exact congrArg Units.val (h₁.trans h₂)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.Transition
