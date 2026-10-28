import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualOpen.ScalarTransitions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ScalarCoefficientSnd

/-! # Scalar Cech Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ScalarCechCoefficients

noncomputable section

/-! The actual scalar pullback cocycle multiplies first-order
coefficients by restrictions of the original global complex constant. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

theorem lineFrameDualCech_scalar (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType X.hom] [IsReduced X.left]
    [IsAffineHom (pullback.diagonal (terminal.from (LieRanks.dualNumberTest ℂ ⊗ X).left))]
    (M : (LieRanks.dualNumberTest ℂ ⊗ X).left.Modules) {I : Type}
    (U : I → (LieRanks.dualNumberTest ℂ ⊗ X).left.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (e : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule (U i).toScheme)
    (a : Fin 2 → I) (c : ℂ) :
    (LineFrameDualCech.lineFrameDualCech X (fun i => TensorCechCoefficients.localFrameFromPullback (U i)
      (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame (Scalars.dualFamilyScalar X c).left (U i).ι (U i).ι
        (DualOpen.Scalars.dualOpenScalar X (U i) c) (DualOpen.Scalars.dualOpenScalar_ι X (U i) c) M (e i))) hU a).val.snd =
      X.left.presheaf.map (homOfLE (show AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (CechCoefficient.dualReducedCechCover X U) a ≤ ⊤ from le_top)).op
        (Open.ComplexConstants.complexGlobalSectionMap X c) *
          (show Γ(X.left, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (CechCoefficient.dualReducedCechCover X U) a) from
            (LineFrameDualCech.lineFrameDualCech X (fun i => TensorCechCoefficients.localFrameFromPullback (U i) (e i)) hU a).val.snd) := by
  have h := DualOpen.ScalarTransitions.dualScalarPullbackFrame_transition X M (U (a 0)) (U (a 1)) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1) c (e (a 0)) (e (a 1))
  have h₁ := congrArg (fun u => (Units.map (CechCoefficient.dualCechSectionCoefficientEquiv X U hU a).toMonoidHom u).val.snd) h
  have h₂ := ScalarCoefficientSnd.dualCechSectionCoefficient_scalar_snd X U hU a c
    ((TensorCechCoefficients.localFrameFromPullback (U (a 0)) (e (a 0))).transition (TensorCechCoefficients.localFrameFromPullback (U (a 1)) (e (a 1)))
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)).val
  exact h₁.trans h₂

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ScalarCechCoefficients
