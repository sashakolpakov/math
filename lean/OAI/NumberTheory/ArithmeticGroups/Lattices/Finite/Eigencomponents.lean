import Mathlib

/-! # Eigencomponents -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.Eigencomponents.Construction

noncomputable section

/-! An invariant subspace contains each component of a finite sum of
eigenvectors with distinct eigenvalues. This will recover integer
weight components of a matrix-group vanishing ideal. -/

open scoped Classical

theorem finite_eigencomponents_mem
    {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V]
    (f : V →ₗ[k] V) (W : Submodule k V) (hW : ∀ x ∈ W, f x ∈ W)
    (eigenvalue : ι → k) (hdistinct : Function.Injective eigenvalue) (s : Finset ι)
    (x : ι → V) (hx : ∀ i, f (x i) = eigenvalue i • x i)
    (hs : ∑ i ∈ s, x i ∈ W) : ∀ i ∈ s, x i ∈ W := by
  induction s using Finset.induction_on generalizing x with
  | empty => simp
  | @insert a s ha ih =>
    let y : ι → V := fun i => (eigenvalue i - eigenvalue a) • x i
    have hy : ∀ i, f (y i) = eigenvalue i • y i := by
      intro i
      simp only [y, map_smul, hx, smul_smul]
      rw [mul_comm]
    have hys : ∑ i ∈ s, y i ∈ W := by
      have hmem := W.sub_mem (hW _ hs) (W.smul_mem (eigenvalue a) hs)
      have he : (∑ i ∈ s, y i) = f (∑ i ∈ insert a s, x i) -
          eigenvalue a • (∑ i ∈ insert a s, x i) := by
        simp only [y, sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum,
          Finset.sum_insert ha, map_add, map_sum, hx, smul_add]
        module
      rw [he]
      exact hmem
    have hsmall (i : ι) (hi : i ∈ s) : x i ∈ W := by
      have hi_ne : i ≠ a := fun h => ha (h ▸ hi)
      have hc : eigenvalue i - eigenvalue a ≠ 0 := sub_ne_zero.mpr (fun h => hi_ne (hdistinct h))
      have hiy := ih y hy hys i hi
      have hh := W.smul_mem (eigenvalue i - eigenvalue a)⁻¹ hiy
      simpa only [y, inv_smul_smul₀ hc] using hh
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have hh := W.sub_mem hs (W.sum_mem (fun j hj => hsmall j hj))
      simpa only [Finset.sum_insert ha, add_sub_cancel_right] using hh
    · exact hsmall i hi

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.Eigencomponents.Construction
