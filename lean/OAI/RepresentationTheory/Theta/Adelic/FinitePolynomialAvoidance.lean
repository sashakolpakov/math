import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! # Finite Polynomial Avoidance -/

namespace OAI.RepresentationTheory.Theta.Adelic.FinitePolynomialAvoidance

noncomputable section

/-! A finite set of more than the combined polynomial degrees contains
a point avoiding two independently parametrized root sets. -/

open scoped Classical

variable {k I : Type*} [Field k] [Fintype I]

theorem root_indices_card_le (p : Polynomial k) (hp : p ≠ 0)
    (a : I → k) (ha : Function.Injective a) :
    (Finset.univ.filter (fun i => p.eval (a i) = 0)).card ≤ p.natDegree := by
  let s := Finset.univ.filter (fun i => p.eval (a i) = 0)
  have hsub : s.image a ⊆ p.roots.toFinset := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr (Finset.mem_filter.mp hi).2)
  calc
    s.card = (s.image a).card := (Finset.card_image_of_injective s ha).symm
    _ ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ p.roots.card := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p

theorem two_polynomial_avoidance (p q : Polynomial k) (hp : p ≠ 0) (hq : q ≠ 0)
    (a b : I → k) (ha : Function.Injective a) (hb : Function.Injective b)
    (hcard : p.natDegree + q.natDegree < Fintype.card I) :
    ∃ i, p.eval (a i) ≠ 0 ∧ q.eval (b i) ≠ 0 := by
  by_contra! h
  let s := Finset.univ.filter (fun i => p.eval (a i) = 0)
  let t := Finset.univ.filter (fun i => q.eval (b i) = 0)
  have he : s ∪ t = Finset.univ := by
    ext i
    simp only [s, t, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true]
    by_cases hi : p.eval (a i) = 0
    · exact Or.inl hi
    · exact Or.inr (h i hi)
  have hc : Fintype.card I ≤ s.card + t.card := by
    rw [← Finset.card_univ, ← he]
    exact Finset.card_union_le _ _
  have hs := root_indices_card_le p hp a ha
  have ht := root_indices_card_le q hq b hb
  change s.card ≤ p.natDegree at hs
  change t.card ≤ q.natDegree at ht
  omega

theorem polynomial_avoidance (p : Polynomial k) (hp : p ≠ 0)
    (a : I → k) (ha : Function.Injective a) (hcard : p.natDegree < Fintype.card I) :
    ∃ i, p.eval (a i) ≠ 0 := by
  obtain ⟨i, hi, _⟩ := two_polynomial_avoidance p 1 hp one_ne_zero a a ha ha
    (by simpa using hcard)
  exact ⟨i, hi⟩

end

end OAI.RepresentationTheory.Theta.Adelic.FinitePolynomialAvoidance
