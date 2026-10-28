import OAI.AlgebraicGeometry.Comparison.Betti.PuncturedParametricDbar
import OAI.AlgebraicGeometry.Comparison.Betti.Pure.VectorCauchy

/-! # Coordinate Line Cauchy -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Pure.CoordinateLineCauchy.Dolbeault

noncomputable section

/-! The actual global parametric primitive preserves the original pure
bidegree of differential-form coefficients through their character kernels. -/

open _root_.TopologicalSpace Set
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]
  {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℂ P]
  [IsScalarTower ℝ ℂ P] [FiniteDimensional ℝ P]

theorem coordinateLineCauchyCandidate_pure (S : Opens P) (b : Bool) (p q : ℕ) (g : P × ℂ → Analysis.DifferentialForms.Manifold.Basic.FormValue E (p + q))
    (hg : ContDiffOn ℝ ∞ g ((S : Set P) ×ˢ (PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen b : Set ℂ)))
    (x : P × ℂ) (hx : x.1 ∈ S) (hpure : ∀ w ∈ PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen b, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q (g (x.1, w))) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q (PuncturedParametricDbar.Dolbeault.coordinateLineCauchyCandidate S b g hg x) := by
  intro z v
  let L : Analysis.DifferentialForms.Manifold.Basic.FormValue E (p + q) →L[ℂ] Analysis.DifferentialForms.Manifold.Basic.FormValue E (p + q) :=
    VectorCauchy.Dolbeault.scalarCovectorPullbackCLM (p + q) z -
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z • ContinuousLinearMap.id ℂ (Analysis.DifferentialForms.Manifold.Basic.FormValue E (p + q))
  have hzero : ∀ w ∈ PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen b, L (g (x.1, w)) = 0 := by
    intro w hw
    ext u
    change g (x.1, w) (fun i => (z : ℂ) • u i) - Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * g (x.1, w) u = 0
    rw [hpure w hw z u, sub_self]
  have h := PuncturedParametricDbar.Dolbeault.coordinateLineCauchyCandidate_kernel L S b g hg x hx hzero
  have hv := congrArg (fun a : Analysis.DifferentialForms.Manifold.Basic.FormValue E (p + q) => a v) h
  change PuncturedParametricDbar.Dolbeault.coordinateLineCauchyCandidate S b g hg x (fun i => (z : ℂ) • v i) -
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter p q z * PuncturedParametricDbar.Dolbeault.coordinateLineCauchyCandidate S b g hg x v = 0 at hv
  exact sub_eq_zero.mp hv

end

end OAI.AlgebraicGeometry.Comparison.Betti.Pure.CoordinateLineCauchy.Dolbeault
