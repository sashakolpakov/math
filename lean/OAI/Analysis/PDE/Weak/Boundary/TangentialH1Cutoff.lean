import OAI.Analysis.PDE.Weak.Elliptic.H1Derivative
import OAI.Analysis.PDE.Weak.Elliptic.VectorDifference
import OAI.Analysis.PDE.Weak.Boundary.H1Translation

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- The localized energy bound controls the whole differentiated H¹
graph, including the terms in which a derivative hits the cutoff. -/
theorem exists_H1_tangential_derivative_cutoff
    (ℓ : OAI.Analysis.PDE.Variational.CellCoordinates m →L[ℝ] ℝ)
    (p : H1Pair m) (hp : p ∈ H1Zero {x | 0 < ℓ x})
    (η : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    {M K L J C : ℝ} (hM : ∀ x, |η x| ≤ M)
    (hK : ∀ x, ‖OAI.Analysis.PDE.Variational.cellGradient η x‖ ≤ K)
    (j : Fin (m + 1)) (htangent : ℓ (Pi.single j 1) = 0) {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝 0)) (hs0 : ∀ n, s n ≠ 0)
    (hL : ∀ n x, |differenceQuotient (Pi.single j 1) (s n) η x| ≤ L)
    (hJ : ∀ n x, ‖differenceQuotient (Pi.single j 1) (s n) (OAI.Analysis.PDE.Variational.cellGradient η) x‖ ≤ J)
    (hC : ∀ n, ‖cutoffL2 η hη.continuous hM
      (differenceQuotientL2 volume (Pi.single j 1) (s n) p.2)‖ ≤ C) :
    ∃ q : H1Pair m, q ∈ H1Zero {x | 0 < ℓ x} ∧
      HasWeakDirectionalDerivative volume (Pi.single j 1)
        (cutoffH1Pair η (hη.of_le (by simp)) hM hK p).1 q.1 ∧
      HasWeakDirectionalDerivative volume (Pi.single j 1)
        (cutoffH1Pair η (hη.of_le (by simp)) hM hK p).2 q.2 := by
  let pη := cutoffH1Pair η (hη.of_le (by simp)) hM hK p
  have hpη : pη ∈ H1Zero {x | 0 < ℓ x} :=
    OAI.Analysis.PDE.Weak.H1Zero.cutoff hp η hη hM hK inter_subset_right
  have hv0 : Integrable (pη.1 : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) :=
    integrable_cutoffL2 volume η hη.continuous hηs hM p.1
  have hv1 : Integrable (pη.2 : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m) := by
    have ha := integrable_cutoffL2 volume η hη.continuous hηs hM p.2
    have hb := integrable_vectorProductL2 volume (OAI.Analysis.PDE.Variational.cellGradient η)
      (OAI.Analysis.PDE.Variational.continuous_cellGradient (hη.of_le (by simp)))
      (hasCompactSupport_cellGradient hηs) hK p.1
    exact (ha.add hb).congr (Lp.coeFn_add _ _).symm
  apply exists_H1_derivative_of_difference_bounds pη hv0 hv1 (Pi.single j 1) hs hs0
    (fun n ↦ OAI.Analysis.PDE.Weak.H1Zero.tangential_difference ℓ hpη (Pi.single j 1) htangent (s n))
    (fun n ↦ OAI.Analysis.PDE.Weak.H1Zero.difference_bound hpη j (hs0 n))
  intro n
  change ‖differenceQuotientL2 volume (Pi.single j 1) (s n)
    (cutoffL2 η hη.continuous hM p.2 +
      vectorProductL2 (OAI.Analysis.PDE.Variational.cellGradient η) (OAI.Analysis.PDE.Variational.continuous_cellGradient (hη.of_le (by simp))) hK p.1)‖ ≤
    (C + L * ‖p.2‖) + (K * ‖p.2‖ + J * ‖p.1‖)
  rw [map_add]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (norm_differenceQuotientL2_cutoff_le volume η hη.continuous hM
      (Pi.single j 1) (s n) (hL n) p.2).trans (add_le_add (hC n) le_rfl)
  · apply (norm_differenceQuotientL2_vectorProduct_le volume (OAI.Analysis.PDE.Variational.cellGradient η)
      (OAI.Analysis.PDE.Variational.continuous_cellGradient (hη.of_le (by simp))) hK
      (Pi.single j 1) (s n) (hJ n) p.1).trans
    exact add_le_add
      (mul_le_mul_of_nonneg_left (OAI.Analysis.PDE.Weak.H1Zero.difference_bound hp j (hs0 n))
        ((norm_nonneg _).trans (hK 0))) le_rfl

end OAI.Analysis.PDE.Weak
