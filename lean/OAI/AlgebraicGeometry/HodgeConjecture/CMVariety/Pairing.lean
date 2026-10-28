import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Algebra.DirectSum.Module

/-! # Pairing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Pairing.CM.Abelian

/-! A nondegenerate pairing detects the diagonal part of a spanning decomposition. -/

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

theorem mem_diagonal_of_annihilates_offDiagonal
    (B : V →ₗ[K] W →ₗ[K] K)
    (P Poff : Submodule K V) (Q Qoff : Submodule K W)
    (hV : P ⊔ Poff = ⊤) (hW : Q ⊔ Qoff = ⊤)
    (hsep : ∀ v, (∀ w, B v w = 0) → v = 0)
    (hPQoff : ∀ v ∈ P, ∀ w ∈ Qoff, B v w = 0)
    (hPoffQ : ∀ v ∈ Poff, ∀ w ∈ Q, B v w = 0)
    (v : V) (hv : ∀ w ∈ Qoff, B v w = 0) : v ∈ P := by
  have hvmem : v ∈ P ⊔ Poff := hV ▸ Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hvmem
  have hb0 : b = 0 := by
    apply hsep b
    intro w
    have hwmem : w ∈ Q ⊔ Qoff := hW ▸ Submodule.mem_top
    obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hwmem
    rw [map_add, hPoffQ b hb c hc, zero_add]
    have h := hv d hd
    rw [map_add, LinearMap.add_apply, hPQoff a ha d hd, zero_add] at h
    exact h
  simpa only [hb0, add_zero] using ha

theorem distinguished_sup_others_eq_top {ι : Type*}
    (A : ι → Submodule K V) (hA : iSup A = ⊤) (i : ι) :
    A i ⊔ (⨆ j, ⨆ (_ : j ≠ i), A j) = ⊤ := by
  apply top_unique
  rw [← hA]
  apply iSup_le
  intro j
  by_cases hji : j = i
  · subst j
    exact le_sup_left
  · calc
      A j ≤ ⨆ (_ : j ≠ i), A j := le_iSup (fun _ : j ≠ i => A j) hji
      _ ≤ ⨆ k, ⨆ (_ : k ≠ i), A k := le_iSup (fun k => ⨆ (_ : k ≠ i), A k) j
      _ ≤ A i ⊔ (⨆ k, ⨆ (_ : k ≠ i), A k) := le_sup_right

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.Pairing.CM.Abelian
