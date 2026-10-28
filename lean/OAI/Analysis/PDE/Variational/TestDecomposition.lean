import OAI.Analysis.PDE.Variational.CellL2
import Mathlib.Geometry.Manifold.PartitionOfUnity

open Set _root_.MeasureTheory
open scoped ContDiff Manifold
noncomputable section
namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- A compact smooth test splits into finitely many compact smooth tests
subordinate to any open covering of its support. -/
theorem smooth_test_decomposition {ι : Type*}
    (U : ι→Set (CellCoordinates m)) (hU : ∀ i, IsOpen (U i))
    (φ : CellCoordinates m→ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hcover : tsupport φ ⊆ ⋃ i, U i) :
    ∃ s : Finset ι, ∃ ψ : s→CellCoordinates m→ℝ,
      (∀ i, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧ tsupport (ψ i)⊆U i) ∧
      φ=fun x ↦ ∑ i, ψ i x := by
  classical
  obtain ⟨s,hs⟩ := hc.elim_finite_subcover U hU hcover
  have hcover' : tsupport φ ⊆ ⋃ i:s, U i := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨hi,hxi⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,hxi⟩
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ,CellCoordinates m)) (isClosed_tsupport φ) (fun i:s ↦ U i) (fun i ↦ hU i) hcover'
  let ψ : s→CellCoordinates m→ℝ := fun i x ↦ ρ i x*φ x
  refine ⟨s,ψ,?_,?_⟩
  · intro i
    have hi : ContDiff ℝ ∞ (ρ i) := contMDiff_iff_contDiff.mp (ρ i).contMDiff
    exact ⟨hi.mul hφ,hc.mul_left,(tsupport_mul_subset_left).trans (hρ i)⟩
  · funext x
    change φ x=∑ i:s, ρ i x*φ x
    rw [← Finset.sum_mul]
    by_cases hx : φ x=0
    · simp only [hx,mul_zero]
    · have hsum := ρ.sum_eq_one (subset_tsupport φ hx)
      rw [finsum_eq_sum_of_fintype] at hsum
      rw [hsum,one_mul]

end OAI.Analysis.PDE.Variational
