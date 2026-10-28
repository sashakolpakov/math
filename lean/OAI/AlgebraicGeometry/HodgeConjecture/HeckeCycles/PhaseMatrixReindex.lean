import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction
import OAI.RepresentationTheory.Theta.Adelic.DataTheta

/-! # Phase Matrix Reindex -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PhaseMatrixReindex.CM

noncomputable section

section

/-! Reindex the actual phase coordinates and exchange position and momentum.
The exchange reverses the alternating form. -/

open scoped Classical

variable {I J : Type}

def swap (e : I ≃ J) : ((J ⊕ J) → ℚ) ≃ₗ[ℚ] ((I ⊕ I) → ℚ) :=
  LinearEquiv.funCongrLeft ℚ ℚ ((Equiv.sumCongr e e).trans (Equiv.sumComm J J))

theorem swap_inl (e : I ≃ J) (x : (J ⊕ J) → ℚ) (i : I) :
    swap e x (.inl i) = x (.inr (e i)) := rfl

theorem swap_inr (e : I ≃ J) (x : (J ⊕ J) → ℚ) (i : I) :
    swap e x (.inr i) = x (.inl (e i)) := rfl

variable [Fintype I] [Fintype J]

theorem swap_pairing (e : I ≃ J) (x y : (J ⊕ J) → ℚ) :
    Source.ComplexAction.CM.Symplectic.pairing (swap e x) (swap e y) =
      -RepresentationTheory.Theta.Adelic.DataTheta.standardPairing x y := by
  change (∑ i, (x (.inr (e i)) * y (.inl (e i)) -
    y (.inr (e i)) * x (.inl (e i)))) = _
  rw [e.sum_comp (fun j => x (.inr j) * y (.inl j) - y (.inr j) * x (.inl j))]
  unfold RepresentationTheory.Theta.Adelic.DataTheta.standardPairing
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end

/-! Evaluation of a reindexed phase matrix on the exchanged coordinates. -/

open scoped Classical _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.DataTheta

variable {I J : Type} [Fintype I] [Fintype J]

theorem action (e : I ≃ J) (A : Matrix (J ⊕ J) (J ⊕ J) ℚ)
    (x : (J ⊕ J) → ℚ) :
    A.submatrix (e.sumCongr e) (e.sumCongr e) *ᵥ swap e x =
      (A *ᵥ RepresentationTheory.Theta.Adelic.DataTheta.swapPhase x) ∘ (e.sumCongr e) := by
  rw [Matrix.submatrix_mulVec_equiv]
  have he : swap e x ∘ (e.sumCongr e).symm = RepresentationTheory.Theta.Adelic.DataTheta.swapPhase x := by
    funext i
    cases i <;> simp [swap, RepresentationTheory.Theta.Adelic.DataTheta.swapPhase]
  rw [he]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PhaseMatrixReindex.CM
