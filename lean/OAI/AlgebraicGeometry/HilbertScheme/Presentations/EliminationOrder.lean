import OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedOrder
import Mathlib.Algebra.MvPolynomial.Supported

/-! # Elimination Order -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EliminationOrder.GradedHilbert

noncomputable section

/-! Elimination orders and a support criterion for polynomials independent of selected variables. -/

open _root_.MvPolynomial
open scoped MonomialOrder

variable {n : ℕ}

def eliminatedWeight (s : Finset (Fin (n + 1))) : (Fin (n + 1) →₀ ℕ) →+ ℕ where
  toFun a := ∑ i ∈ s, a i
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]

def eliminationOrder (s : Finset (Fin (n + 1))) : MonomialOrder (Fin (n + 1)) :=
  WeightedOrder.GradedHilbert.prependWeight MonomialOrder.lex (eliminatedWeight s)

theorem eliminatedWeight_eq_zero (s : Finset (Fin (n + 1))) (a : Fin (n + 1) →₀ ℕ) :
    eliminatedWeight s a = 0 ↔ ∀ i ∈ s, a i = 0 := by
  exact Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)

theorem eliminatedWeight_zero_of_le (s : Finset (Fin (n + 1)))
    {a b : Fin (n + 1) →₀ ℕ} (hab : a ≼[eliminationOrder s] b)
    (hb : eliminatedWeight s b = 0) : eliminatedWeight s a = 0 := by
  rw [eliminationOrder, WeightedOrder.GradedHilbert.prependWeight_le_iff, hb] at hab
  exact (hab.resolve_left (Nat.not_lt_zero _)).1

variable {K : Type*} [Field K]

theorem supported_complement_iff_eliminatedWeight (s : Finset (Fin (n + 1)))
    (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :
    f ∈ supported K ((s : Set (Fin (n + 1)))ᶜ) ↔
      ∀ a ∈ f.support, eliminatedWeight s a = 0 := by
  rw [mem_supported]
  constructor
  · intro hf a ha
    apply (eliminatedWeight_eq_zero s a).mpr
    intro i hi
    by_contra hne
    exact hf ((mem_vars_iff_mem_support i).mpr ⟨a, ha, Finsupp.mem_support_iff.mpr hne⟩) hi
  · intro hf i hi his
    obtain ⟨a, ha, hia⟩ := (mem_vars_iff_mem_support i).mp hi
    exact Finsupp.mem_support_iff.mp hia ((eliminatedWeight_eq_zero s a).mp (hf a ha) i his)

theorem supported_complement_iff_leadingWeight (s : Finset (Fin (n + 1)))
    (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :
    f ∈ supported K ((s : Set (Fin (n + 1)))ᶜ) ↔
      eliminatedWeight s ((eliminationOrder s).degree f) = 0 := by
  rw [supported_complement_iff_eliminatedWeight]
  constructor
  · intro hf
    by_cases hf0 : f = 0
    · simp [hf0]
    · exact hf _ ((eliminationOrder s).degree_mem_support hf0)
  · intro hf a ha
    exact eliminatedWeight_zero_of_le s ((eliminationOrder s).le_degree ha) hf

theorem supported_complement_of_degree_le (s : Finset (Fin (n + 1)))
    {f g : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n} (hfg : (eliminationOrder s).degree f ≼[eliminationOrder s]
      (eliminationOrder s).degree g) (hg : g ∈ supported K ((s : Set (Fin (n + 1)))ᶜ)) :
    f ∈ supported K ((s : Set (Fin (n + 1)))ᶜ) := by
  apply (supported_complement_iff_leadingWeight s f).mpr
  exact eliminatedWeight_zero_of_le s hfg ((supported_complement_iff_leadingWeight s g).mp hg)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EliminationOrder.GradedHilbert
