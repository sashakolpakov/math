import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameDualCech
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.Transition
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.CoefficientReduction

/-! # Cech -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.Cech

noncomputable section

/-! The Cech cocycle of the constructed normalized affine frames
has constant coefficient one in the original reduced coefficient rings. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace
open _root_.CategoryTheory.MonoidalCategory

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]

theorem dualCechUnitCoefficient_normalized {I : Type}
    (U : I → (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : ∀ i, IsAffineOpen (U i))
    {n : ℕ} (a : Fin (n + 1) → I)
    (u : Γ((LieRanks.dualNumberTest ℂ ⊗ X).left, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)ˣ)
    (hu : (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left.app (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) u.val = 1) :
    (Units.map (Dual.CechCoefficient.dualCechSectionCoefficientEquiv X U hU a).toMonoidHom u).val.fst = 1 := by
  change Regular.SectionTransport.regularSectionTransport (Dual.CechCoefficient.dualReducedCechIntersection X U a)
    (DualOpen.SectionEquivalence.dualOpenSectionCoefficientEquiv X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)
      (Dual.CechCoefficient.dualCechIntersection_affine X U hU a) u.val).fst = 1
  exact (congrArg (Regular.SectionTransport.regularSectionTransport (Dual.CechCoefficient.dualReducedCechIntersection X U a))
    (DualOpen.CoefficientReduction.dualOpenUnit_normalized X (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)
      (Dual.CechCoefficient.dualCechIntersection_affine X U hU a) u hu)).trans (map_one _)

variable (L : HilbertConstruction.Line.Bundles.LineBundle (LieRanks.dualNumberTest ℂ ⊗ X).left)
    (e₀ : (Scheme.Modules.pullback (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction X).left).obj L.sheaf ≅
      ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X.left)

theorem normalizedDualFrames_cech {I : Type} (s : I → Dual.NormalizedFrameCover.NormalizedDualFrame X L e₀) :
    Dual.UnitCechCoefficients.DualUnitCechNormalized X.left.sheaf.obj (Dual.CechCoefficient.dualReducedCechCover X (fun i => (s i).domain))
      (LineFrameDualCech.lineFrameDualCech X (fun i => (s i).localFrame X L e₀) (fun i => (s i).affine)) := by
  intro a
  exact dualCechUnitCoefficient_normalized X (fun i => (s i).domain) (fun i => (s i).affine) a
    ((s (a 0)).localFrame X L e₀ |>.transition ((s (a 1)).localFrame X L e₀)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => (s i).domain) a)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 0)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 1))
    (Transition.normalizedDualFrame_transition_reduces X L e₀ (s (a 0)) (s (a 1))
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (fun i => (s i).domain) a)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 0)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le (fun i => (s i).domain) a 1))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NormalizedDual.Cech
