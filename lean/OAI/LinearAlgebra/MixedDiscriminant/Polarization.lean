import Mathlib

noncomputable section
open Finset

namespace OAI.LinearAlgebra.MixedDiscriminant

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem multilinear_subset_expansion {n : ℕ}
    (M : MultilinearMap ℝ (fun _ : Fin n => E) ℝ) (v : Fin n → E)
    (S : Finset (Fin n)) :
    M (fun _ => ∑ j ∈ S, v j) =
      ∑ f : Fin n → Fin n with (∀ i, f i ∈ S), M (fun i => v (f i)) := by
  classical
  have h := M.map_sum_finset (fun _ j => v j) (fun _ => S)
  convert h using 2
  ext f
  simp [Fintype.mem_piFinset]

theorem sum_permutation_eq_sum_surjective {n : ℕ} (F : (Fin n → Fin n) → ℝ) :
    (∑ σ : Equiv.Perm (Fin n), F σ) = ∑ f : Fin n → Fin n with Function.Surjective f, F f := by
  classical
  apply Finset.sum_bij (fun (σ : Equiv.Perm (Fin n)) _ => (σ : Fin n → Fin n))
  · intro σ hσ
    simp [σ.surjective]
  · intro σ hσ τ hτ h
    exact Equiv.ext (congrFun h)
  · intro f hf
    have hs : Function.Surjective f := (Finset.mem_filter.mp hf).2
    let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f
      ⟨(Finite.injective_iff_surjective).mpr hs,hs⟩
    exact ⟨σ,Finset.mem_univ _,rfl⟩
  · intro σ hσ
    rfl

/-- Inclusion-exclusion isolates exactly the permutations among all choices
of one vector in each multilinear argument. -/
theorem multilinear_polarization_sum {n : ℕ}
    (M : MultilinearMap ℝ (fun _ : Fin n => E) ℝ) (v : Fin n → E) :
    (∑ S : Finset (Fin n), (-1 : ℝ) ^ (n - S.card) *
      M (fun _ => ∑ i ∈ S, v i)) =
      ∑ σ : Equiv.Perm (Fin n), M (fun i => v (σ i)) := by
  classical
  let A : Fin n → Finset (Fin n → Fin n) :=
    fun j => Finset.univ.filter (fun f => ∀ i, f i ≠ j)
  have hleft : (Finset.univ.inf fun j => (A j)ᶜ) =
      Finset.univ.filter (fun f : Fin n → Fin n => Function.Surjective f) := by
    ext f
    simp only [Finset.mem_inf,Finset.mem_univ,true_implies,Finset.mem_compl,
      A,Finset.mem_filter,true_and]
    change (∀ j, ¬ ∀ i, f i ≠ j) ↔ Function.Surjective f
    simp only [not_forall,not_not]
    rfl
  have hinner (S : Finset (Fin n)) : S.inf A =
      Finset.univ.filter (fun f : Fin n → Fin n => ∀ i, f i ∈ Sᶜ) := by
    ext f
    simp only [Finset.mem_inf,A,Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_compl]
    aesop
  have h := Finset.inclusion_exclusion_sum_inf_compl Finset.univ A
    (fun f : Fin n → Fin n => M (fun i => v (f i)))
  rw [hleft] at h
  simp only [hinner,← multilinear_subset_expansion M v] at h
  have hpow : (Finset.univ : Finset (Fin n)).powerset = Finset.univ := by
    ext S
    simp
  rw [hpow] at h
  simp only [zsmul_eq_mul,Int.cast_pow,Int.cast_neg,Int.cast_one] at h
  rw [← sum_permutation_eq_sum_surjective] at h
  rw [h]
  symm
  apply Finset.sum_bij (fun S _ => Sᶜ)
  · intro S hS
    exact Finset.mem_univ _
  · intro S hS T hT hST
    exact compl_injective hST
  · intro S hS
    exact ⟨Sᶜ,Finset.mem_univ _,compl_compl S⟩
  · intro S hS
    have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
    simp [Finset.card_compl,Nat.sub_sub_self hcard]

theorem symmetric_multilinear_polarization {n : ℕ}
    (M : MultilinearMap ℝ (fun _ : Fin n => E) ℝ)
    (hsym : ∀ v (σ : Equiv.Perm (Fin n)), M (fun i => v (σ i)) = M v)
    (v : Fin n → E) :
    ((n.factorial : ℝ)⁻¹ * ∑ S : Finset (Fin n),
      (-1 : ℝ) ^ (n - S.card) * M (fun _ => ∑ i ∈ S, v i)) = M v := by
  rw [multilinear_polarization_sum]
  simp only [hsym,Finset.sum_const,Finset.card_univ,Fintype.card_perm,
    Fintype.card_fin,nsmul_eq_mul]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

end OAI.LinearAlgebra.MixedDiscriminant
