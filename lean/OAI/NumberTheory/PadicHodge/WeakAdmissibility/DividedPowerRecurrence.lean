import OAI.NumberTheory.PadicHodge.WeakAdmissibility.RestrictedCoefficients

/-! # Divided Power Recurrence -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.DividedPowerRecurrence

noncomputable section

/-! Restrictedness of the recurrence occurring in divided-power division by X-xi. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.RestrictedCoefficients
variable {R : Type*} [CommRing R]
variable (p : ℕ) [Fact p.Prime] (ξ : R)

theorem recurrence_restricted (a b : ℕ → R)
    (ha : RestrictedCoefficients.IsRestricted (p : R) a)
    (hcancel : ∀ (r : ℕ) (x : R), (p : R) ^ r ∣ ξ * x → (p : R) ^ r ∣ x)
    (hrec : ∀ n : ℕ, ξ * b (n + 1) = a (n + 1) + (n + 1 : ℕ) * b n) :
    RestrictedCoefficients.IsRestricted (p : R) b := by
  intro r
  induction r with
  | zero => exact ⟨0, fun _ _ => by simp only [pow_zero, one_dvd]⟩
  | succ r ih =>
    obtain ⟨Na, hNa⟩ := ha (r + 1)
    obtain ⟨Nb, hNb⟩ := ih
    let N := max Na Nb
    let M := p * (N + 1)
    have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
    have hNM : N + 1 ≤ M := by
      dsimp only [M]
      exact Nat.le_mul_of_pos_left _ hp
    have hMpos : 0 < M := lt_of_lt_of_le (Nat.succ_pos N) hNM
    have hprev : Nb ≤ M - 1 := by dsimp only [N] at hNM; omega
    have hstart : (p : R) ^ (r + 1) ∣ b M := by
      apply hcancel
      have he := hrec (M - 1)
      rw [Nat.sub_add_cancel hMpos] at he
      rw [he]
      apply dvd_add (hNa M (by dsimp only [N] at hNM; omega))
      have hdp : (p : R) ∣ (M : R) := by
        refine ⟨(N + 1 : ℕ), ?_⟩
        simp only [M, Nat.cast_mul]
      rw [pow_succ']
      exact mul_dvd_mul hdp (hNb (M - 1) hprev)
    refine ⟨M, fun n hn => ?_⟩
    induction n, hn using Nat.le_induction with
    | base => exact hstart
    | succ n hn ih =>
      apply hcancel
      rw [hrec]
      exact dvd_add (hNa (n + 1) (by dsimp only [N] at hNM; omega))
        (dvd_mul_of_dvd_right ih (n + 1 : ℕ))

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.DividedPowerRecurrence
