import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicTensorComplexCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ReindexTheta
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MovingTotalPeriod

/-! # Indexed Graph Relation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IndexedGraphRelation.CM

noncomputable section

/-! Extract the literal reindexed Siegel graph equation from equality
of phase vectors, retaining the required position/momentum swap. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.DataTheta

theorem reindexed_swapped_graph_equation {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (Z : Matrix J J ℂ) (α : (I ⊕ I) → ℂ) (t : J → ℂ)
    (h : RepresentationTheory.Theta.Adelic.DataTheta.swapPhase (fun i => α ((e.sumCongr e).symm i)) = Sum.elim t (Z.mulVec t)) :
    (Z.submatrix e e).mulVec (fun i => α (.inr i)) = fun i => α (.inl i) := by
  have ht (i : I) : α (.inr i) = t (e i) := by
    simpa [RepresentationTheory.Theta.Adelic.DataTheta.swapPhase] using congrFun h (.inl (e i))
  have hm (i : I) : α (.inl i) = Z.mulVec t (e i) := by
    simpa [RepresentationTheory.Theta.Adelic.DataTheta.swapPhase] using congrFun h (.inr (e i))
  funext i
  change (∑ j, Z (e i) (e j) * α (.inr j)) = _
  simp only [ht]
  exact (e.sum_comp (fun j => Z (e i) j * t j)).trans (hm i).symm

theorem symplectic_period_eq_of_graph {I : Type} [Fintype I] [DecidableEq I]
    (γ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Sp I ℚ) (Z W : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix I)
    (h : ∀ x : I → ℂ,
      let α := γ.val.map (algebraMap ℚ ℂ) *ᵥ Sum.elim (Z.matrix.mulVec x) x
      W.matrix.mulVec (fun i => α (.inr i)) = fun i => α (.inl i)) :
    W = (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z := by
  apply ReindexTheta.CM.siegel_matrix_ext
  apply Matrix.ext
  intro i j
  let J := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix
  have hJ : J.mulVec (J⁻¹.mulVec (Pi.single j 1)) = Pi.single j 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).denominator_det_isUnit Z), Matrix.one_mulVec]
  have hh := h (J⁻¹.mulVec (Pi.single j 1))
  dsimp only at hh
  rw [MovingTotalPeriod.CM.rational_symplectic_graph_substitution] at hh
  simp only [Sum.elim_inl, Sum.elim_inr] at hh
  change W.matrix.mulVec (J.mulVec (J⁻¹.mulVec (Pi.single j 1))) =
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).transformSiegel Z).matrix.mulVec
      (J.mulVec (J⁻¹.mulVec (Pi.single j 1))) at hh
  rw [hJ] at hh
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using congrFun hh i

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IndexedGraphRelation.CM
