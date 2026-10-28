import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Rational.FrameComplexChange

/-! # Complex Graph Reindex -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComplexGraphReindex.CM

noncomputable section

/-! The exchanged native complex graph is the graph of its literally
reindexed period matrix. -/

open scoped Classical _root_.Matrix

variable {I J : Type} [Fintype I] [Fintype J]

theorem mulVec (e : I ≃ J) (Z : Matrix J J ℂ) (t : J → ℂ) :
    (Z.submatrix e e).mulVec (t ∘ e) = (Z.mulVec t) ∘ e := by
  funext i
  exact e.sum_comp (fun j => Z (e i) j * t j)

theorem graph (e : I ≃ J) (Z : Matrix J J ℂ) (t : J → ℂ) :
    Rational.FrameComplexChange.CM.swap e (Sum.elim t (Z.mulVec t)) =
      Sum.elim ((Z.submatrix e e).mulVec (t ∘ e)) (t ∘ e) := by
  rw [CM.mulVec]
  funext i
  cases i <;> rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComplexGraphReindex.CM
