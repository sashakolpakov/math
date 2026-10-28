import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Nat.Find

/-! # Maximal Commuting Subspace -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MaximalCommutingSubspace.Construction

noncomputable section

/-! A finite-dimensional subspace of an algebra contains a maximal
commuting subspace, characterized by its centralizer in that subspace. -/

open scoped Classical

theorem exists_maximal_commuting_subspace
    {k A : Type*} [Field k] [Ring A] [Algebra k A] [FiniteDimensional k A]
    (p : Submodule k A) :
    ∃ a : Submodule k A, a ≤ p ∧ (∀ x ∈ a, ∀ y ∈ a, Commute x y) ∧
      ∀ x ∈ p, (∀ y ∈ a, Commute x y) → x ∈ a := by
  let Valid (a : Submodule k A) := a ≤ p ∧ ∀ x ∈ a, ∀ y ∈ a, Commute x y
  let Q (d : ℕ) := ∃ a : Submodule k A, Valid a ∧ Module.finrank k a = d
  have hzero : Q 0 := by
    refine ⟨⊥, ⟨bot_le, ?_⟩, by simp⟩
    intro x hx y hy
    have hx0 : x = 0 := hx
    have hy0 : y = 0 := hy
    rw [hx0, hy0]
  let d := Nat.findGreatest Q (Module.finrank k A)
  have hd : Q d := Nat.findGreatest_spec (Nat.zero_le _) hzero
  obtain ⟨a, ha, had⟩ := hd
  have hmax (b : Submodule k A) (hb : Valid b) (hab : a ≤ b) : b = a := by
    have hr : Module.finrank k b ≤ d := Nat.le_findGreatest b.finrank_le ⟨b, hb, rfl⟩
    rw [← had] at hr
    exact (Submodule.eq_of_le_of_finrank_le hab hr).symm
  refine ⟨a, ha.1, ha.2, fun x hxp hxa => ?_⟩
  let b := a ⊔ k ∙ x
  have hb : Valid b := by
    refine ⟨sup_le ha.1 (Submodule.span_le.mpr ?_), ?_⟩
    · rintro _ rfl
      exact hxp
    intro u hu v hv
    obtain ⟨u₀, hu₀, ux, hux, huEq⟩ := Submodule.mem_sup.mp hu
    obtain ⟨v₀, hv₀, vx, hvx, hvEq⟩ := Submodule.mem_sup.mp hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hux
    obtain ⟨e, rfl⟩ := Submodule.mem_span_singleton.mp hvx
    rw [← huEq, ← hvEq]
    apply Commute.add_left
    · exact (ha.2 u₀ hu₀ v₀ hv₀).add_right ((hxa u₀ hu₀).symm.smul_right e)
    · exact ((hxa v₀ hv₀).smul_left c).add_right (((Commute.refl x).smul_left c).smul_right e)
  have hba : b = a := hmax b hb le_sup_left
  rw [← hba]
  exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MaximalCommutingSubspace.Construction
