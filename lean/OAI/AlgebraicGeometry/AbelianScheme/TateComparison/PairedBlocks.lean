import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Pi
import Lean.Util.CollectAxioms

/-! # Paired Blocks -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PairedBlocks

noncomputable section

/-! A nondegenerate form whose distinct blocks are orthogonal restricts
to a nondegenerate pairing between each block and its designated opposite. -/

open scoped BigOperators

variable {F V I : Type*} [Field F] [AddCommGroup V] [Module F V]
  [Fintype I] [DecidableEq I]
  (B : LinearMap.BilinForm F (I → V)) (τ : I → I)

def oppositeBlockPairing (i : I) : LinearMap.BilinForm F V :=
  B.compl₁₂ (LinearMap.single F (fun _ : I => V) (τ i))
    (LinearMap.single F (fun _ : I => V) i)

theorem oppositeBlockPairing_nondegenerate (hτ : Function.Injective τ)
    (hB : B.Nondegenerate)
    (horth : ∀ (i j : I), i ≠ τ j → ∀ (x y : V), B (Pi.single i x) (Pi.single j y) = 0)
    (i : I) : (oppositeBlockPairing B τ i).Nondegenerate := by
  constructor
  · intro x hx
    have hz : Pi.single (τ i) x = (0 : I → V) := by
      apply hB.1
      intro z
      rw [← LinearMap.sum_single_apply (fun _ : I => V) z, map_sum]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j = i
      · subst j
        exact hx (z i)
      · exact horth (τ i) j (fun h => hj (hτ h).symm) x (z j)
    simpa only [Pi.single_eq_same, Pi.zero_apply] using congrFun hz (τ i)
  · intro y hy
    have hz : Pi.single i y = (0 : I → V) := by
      apply hB.2
      intro z
      rw [← LinearMap.sum_single_apply (fun _ : I => V) z, map_sum, LinearMap.sum_apply]
      apply Finset.sum_eq_zero
      intro j _
      by_cases hj : j = τ i
      · subst j
        exact hy (z (τ i))
      · exact horth j i hj (z j) y
    simpa only [Pi.single_eq_same, Pi.zero_apply] using congrFun hz i

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PairedBlocks
