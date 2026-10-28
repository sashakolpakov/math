import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.InitialGenerators
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Existence

/-! # Generator Function -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert

noncomputable section

/-! The Hilbert function of an ideal generated in bounded degrees stabilizes at a field-independent degree, without a saturation hypothesis. -/

open _root_.MvPolynomial

universe u

theorem exponent_sup_degree_le {n : ℕ} (G : Finset (Fin (n + 1) →₀ ℕ)) (B : ℕ)
    (hG : ∀ a ∈ G, a.degree ≤ B) : (G.sup id).degree ≤ (n + 1) * B := by
  have hcoord (i : Fin (n + 1)) : (G.sup id) i ≤ B := by
    apply Finset.sup_induction (p := fun a : Fin (n + 1) →₀ ℕ => a i ≤ B)
    · exact Nat.zero_le B
    · intro a ha c hc
      exact max_le ha hc
    · intro a ha
      exact (Finsupp.le_degree i a).trans (hG a ha)
  rw [Finsupp.degree_eq_sum]
  calc
    _ ≤ ∑ _i : Fin (n + 1), B := Finset.sum_le_sum (fun i _ => hcoord i)
    _ = (n + 1) * B := by simp

def generatorHilbertFunctionBound (n D : ℕ) : ℕ := (n + 1) * Uniform.GroebnerCompletion.GradedHilbert.homogeneousGroebnerDegreeBound n D

variable {K : Type u} [Field K] {n : ℕ}

theorem bounded_generators_hilbertFunction_eq
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))
    (hB : I.toIdeal = Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)))
    (D : ℕ) (hb : ∀ b ∈ B, b ≠ 0 ∧ ∃ d ≤ D, b.IsHomogeneous d)
    (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P)
    (d : ℕ) (hd : generatorHilbertFunctionBound n D ≤ d) :
    (Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d : ℚ) = P.eval (d : ℚ) := by
  let m : MonomialOrder (Fin (n + 1)) := MonomialOrder.lex
  obtain ⟨G, hG, hGdeg⟩ := InitialGenerators.GradedHilbert.exists_uniform_initial_generators m I B hB D hb
  have hPG : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal (Hilbert.Existence.GradedHilbert.monomialHilbertPolynomial G) := by
    apply (InitialIdeal.GradedHilbert.hasHilbertPolynomial_initialIdeal_iff m I _).mp
    rw [hG]
    exact Hilbert.Existence.GradedHilbert.monomialSpan_hasHilbertPolynomial G
  have heq : Hilbert.Existence.GradedHilbert.monomialHilbertPolynomial G = P := Hilbert.Polynomial.GradedHilbert.hilbertPolynomial_unique hPG hP
  rw [← heq, ← InitialIdeal.GradedHilbert.hilbertFunction_initialIdeal m I d, hG]
  change (Hilbert.Polynomial.GradedHilbert.hilbertFunction (Hilbert.MonomialBasis.GradedHilbert.monomialSpan K (G : Set (Fin (n + 1) →₀ ℕ))).toIdeal d : ℚ) = _
  rw [Hilbert.MonomialBasis.GradedHilbert.hilbertFunction_monomialSpan]
  exact Hilbert.Existence.GradedHilbert.card_standard_eventually_polynomial G d ((exponent_sup_degree_le G _ hGdeg).trans hd)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert
