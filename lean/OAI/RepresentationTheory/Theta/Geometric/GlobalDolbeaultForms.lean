import OAI.RepresentationTheory.Theta.Geometric.DolbeaultBoundary

/-! # Global Dolbeault Forms -/

namespace OAI.RepresentationTheory.Theta.Geometric.GlobalDolbeaultForms

noncomputable section

/-! The concrete closed Dolbeault representatives give actual global
pure one-forms, with the same native differential and scalar primitives. -/

set_option backward.isDefEq.respectTransparency false
open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] {M : Type} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ∞ M]

def closedDbarOneGlobal (a : DolbeaultBoundary.ClosedDbarOneForm E M) : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 0 1 :=
  ⟨Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.toGlobal a.val.val,
    fun e he y hy => a.val.property e he y ⟨hy, Set.mem_univ _⟩⟩

theorem closedDbarOneGlobal_onTop (a : DolbeaultBoundary.ClosedDbarOneForm E M) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ (closedDbarOneGlobal a).val = a.val.val :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.onOpen_toGlobal a.val.val

theorem closedDbarOneGlobal_dbar (a : DolbeaultBoundary.ClosedDbarOneForm E M) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (closedDbarOneGlobal a) = 0 := by
  apply Subtype.ext
  rw [Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime_coe, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_self]
  apply (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onTopEquiv (E := E) (M := M)).injective
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤
      (AlgebraicTopology.DeRham.Comparison.DolbeaultProjection.manifoldDolbeaultDoublePrimeForm E M 0 1 (closedDbarOneGlobal a)) =
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ 0
  rw [map_zero]
  have H := AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD_onOpen (⊤ : Opens M) (closedDbarOneGlobal a)
  rw [closedDbarOneGlobal_onTop] at H
  exact H.symm.trans (congrArg Subtype.val a.property)

def globalZeroPureForm (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 0 0 :=
  ⟨f, fun _ _ _ _ => Analysis.DifferentialForms.Manifold.Bidegree.hasBidegree_zero E _⟩

def globalZeroFormOnTop (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) : AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree.AntiOpenManifoldForm E (⊤ : Opens M) 0 :=
  ⟨Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ f,
    AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree.openManifoldHasBidegree_onOpen (globalZeroPureForm f).property ⊤⟩

theorem globalZeroFormOnTop_dbar (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) :
    (DolbeaultBoundary.globalDbarDerivative E M (globalZeroFormOnTop f)).val.val =
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ (Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime (globalZeroPureForm f)).val := by
  change AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen ⊤ f) = _
  rw [Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm.dDoublePrime_coe, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.castDegree_self]
  exact AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldDolbeault.openManifoldDolbeaultD_onOpen ⊤ (globalZeroPureForm f)

end

end OAI.RepresentationTheory.Theta.Geometric.GlobalDolbeaultForms
