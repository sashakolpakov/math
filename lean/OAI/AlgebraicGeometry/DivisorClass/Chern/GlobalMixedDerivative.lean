import OAI.AlgebraicGeometry.DivisorClass.Chern.MixedDerivativeProjection
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection
import OAI.Analysis.DifferentialForms.Manifold.ManifoldSheaf

/-! # Global Mixed Derivative -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalMixedDerivative

noncomputable section

/-! The actual global type parts of a one-form with mixed exterior derivative are Dolbeault closed. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem manifold_two_bidegree_last_zero (A B C : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 2)
    (hA : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 2 0 A.val) (hB : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 1 B.val)
    (hC : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 0 2 C.val) (hs : A + B + C = 0) : C = 0 := by
  apply (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onTopEquiv (E := E) (M := M)).injective
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ C = 0
  apply MixedDerivativeProjection.openManifold_two_bidegree_last_zero (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ A)
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ B) (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ C)
    (Open.ManifoldBidegree.openManifoldHasBidegree_onOpen hA ⊤) (Open.ManifoldBidegree.openManifoldHasBidegree_onOpen hB ⊤)
    (Open.ManifoldBidegree.openManifoldHasBidegree_onOpen hC ⊤)
  simpa only [map_add, map_zero] using congrArg (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen (E := E) (M := M) ⊤) hs

def manifoldOneAntiPure (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1) : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 0 1 :=
  ⟨ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneFormAntiholomorphicPart a, ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneFormAntiholomorphicPart_hasBidegree a⟩

def manifoldOneHoloPure (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1) : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 1 0 :=
  ⟨ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneFormHolomorphicPart a, ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneFormHolomorphicPart_hasBidegree a⟩

theorem manifoldOneAntiPure_dbar_zero_of_mixed (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1)
    (ha : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 1 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a).val) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (manifoldOneAntiPure a) = 0 := by
  let H := manifoldOneHoloPure a
  let A := manifoldOneAntiPure a
  let B : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 1 1 := Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime H + Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime A -
    ⟨Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a, ha⟩
  have hh := Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_add_dDoublePrime H
  have hb := Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime_add_dDoublePrime A
  simp only [Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_self] at hh hb
  have hd := congrArg Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ComplexMultiplication.HodgeComparison.OneFormProjection.CM.Construction.oneForm_parts_add a)
  rw [map_add] at hd
  have hs : (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime H).val + B.val + (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime A).val = 0 := by
    change (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime H).val +
      ((Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime H).val + (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime A).val - Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) +
      (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime A).val = 0
    calc
      _ = ((Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime H).val + (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime H).val) +
        ((Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime A).val + (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime A).val) - Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a := by abel
      _ = 0 := by rw [hh, hb]; exact sub_eq_zero.mpr hd
  apply Subtype.ext
  exact manifold_two_bidegree_last_zero (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime H).val B.val
    (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime A).val (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dPrime H).property B.property
    (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime A).property hs

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GlobalMixedDerivative
