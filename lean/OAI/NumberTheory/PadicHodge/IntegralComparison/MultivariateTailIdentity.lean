import Mathlib.Algebra.MvPolynomial.Funext
import OAI.AlgebraicGeometry.SheafCohomology.Projective.EventualPolynomialIdentity

/-! # Multivariate Tail Identity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MultivariateTailIdentity

noncomputable section

/-! Polynomial identities detected on natural grids and on natural
grids whose distinguished coordinate is sufficiently large. -/

theorem eq_of_nat_eval {ι : Type*} (P Q : MvPolynomial ι ℚ)
    (h : ∀ a : ι → ℕ,
      MvPolynomial.eval (fun i => (a i : ℚ)) P =
        MvPolynomial.eval (fun i => (a i : ℚ)) Q) : P = Q := by
  apply MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → ℚ))
    (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
  intro x hx
  choose a ha using fun i => hx i (Set.mem_univ i)
  have he : x = fun i => (a i : ℚ) := funext (fun i => (ha i).symm)
  rw [he]
  exact h a

theorem eq_of_succ_nat_eval {ι : Type*} (P Q : MvPolynomial ι ℚ)
    (h : ∀ a : ι → ℕ,
      MvPolynomial.eval (fun i => ((a i + 1 : ℕ) : ℚ)) P =
        MvPolynomial.eval (fun i => ((a i + 1 : ℕ) : ℚ)) Q) : P = Q := by
  apply MvPolynomial.funext_set (fun _ => Set.range (fun n : ℕ => ((n + 1 : ℕ) : ℚ)))
    (fun _ => Set.infinite_range_of_injective (fun m n h => by exact Nat.succ.inj (Nat.cast_injective h)))
  intro x hx
  choose a ha using fun i => hx i (Set.mem_univ i)
  have he : x = fun i => ((a i + 1 : ℕ) : ℚ) := funext (fun i => (ha i).symm)
  rw [he]
  exact h a

theorem eq_of_option_tail_eval {ι : Type*} (P Q : MvPolynomial (Option ι) ℚ)
    (h : ∀ a : ι → ℕ, ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      MvPolynomial.eval (fun i => ((Option.elim i n a : ℕ) : ℚ)) P =
        MvPolynomial.eval (fun i => ((Option.elim i n a : ℕ) : ℚ)) Q) : P = Q := by
  apply (MvPolynomial.optionEquivLeft ℚ ι).injective
  apply Polynomial.ext
  intro k
  apply eq_of_nat_eval
  intro a
  obtain ⟨b, hb⟩ := h a
  have hp := AlgebraicGeometry.SheafCohomology.Projective.EventualPolynomialIdentity.Dimension.polynomial_eq_of_eventually_nat_eval_eq
    ((MvPolynomial.optionEquivLeft ℚ ι P).map (MvPolynomial.eval (fun i => (a i : ℚ))))
    ((MvPolynomial.optionEquivLeft ℚ ι Q).map (MvPolynomial.eval (fun i => (a i : ℚ)))) b
    (fun n hn => by
      rw [← MvPolynomial.optionEquivLeft_elim_eval,
        ← MvPolynomial.optionEquivLeft_elim_eval]
      have he : (fun i => Option.elim i (n : ℚ) (fun j => (a j : ℚ))) =
          (fun i => ((Option.elim i n a : ℕ) : ℚ)) := by
        funext i
        cases i <;> rfl
      rw [he]
      exact hb n hn)
  simpa only [Polynomial.coeff_map] using congrArg (fun p => p.coeff k) hp

theorem eq_of_double_option_tail_eval {ι : Type*}
    (P Q : MvPolynomial (Option (Option ι)) ℚ)
    (h : ∀ a : ι → ℕ, ∃ b : ℕ, ∀ n : ℕ, b ≤ n →
      ∃ c : ℕ, ∀ m : ℕ, c ≤ m →
        MvPolynomial.eval (fun i => ((Option.elim i m (fun j => Option.elim j n a) : ℕ) : ℚ)) P =
          MvPolynomial.eval (fun i => ((Option.elim i m (fun j => Option.elim j n a) : ℕ) : ℚ)) Q) :
    P = Q := by
  apply (MvPolynomial.optionEquivLeft ℚ (Option ι)).injective
  apply Polynomial.ext
  intro k
  apply eq_of_option_tail_eval
  intro a
  obtain ⟨b, hb⟩ := h a
  refine ⟨b, fun n hn => ?_⟩
  obtain ⟨c, hc⟩ := hb n hn
  let v : Option ι → ℚ := fun j => ((Option.elim j n a : ℕ) : ℚ)
  have hp := AlgebraicGeometry.SheafCohomology.Projective.EventualPolynomialIdentity.Dimension.polynomial_eq_of_eventually_nat_eval_eq
    ((MvPolynomial.optionEquivLeft ℚ (Option ι) P).map (MvPolynomial.eval v))
    ((MvPolynomial.optionEquivLeft ℚ (Option ι) Q).map (MvPolynomial.eval v)) c
    (fun m hm => by
      rw [← MvPolynomial.optionEquivLeft_elim_eval,
        ← MvPolynomial.optionEquivLeft_elim_eval]
      have he : (fun i => Option.elim i (m : ℚ) v) =
          (fun i => ((Option.elim i m (fun j => Option.elim j n a) : ℕ) : ℚ)) := by
        funext i
        cases i <;> rfl
      rw [he]
      exact hc m hm)
  simpa only [Polynomial.coeff_map] using congrArg (fun p => p.coeff k) hp

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.MultivariateTailIdentity
