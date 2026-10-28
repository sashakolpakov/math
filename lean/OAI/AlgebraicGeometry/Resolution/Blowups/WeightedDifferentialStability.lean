import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialProducts

/-! # Weighted Differential Stability -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.WeightedDifferentialStability.Construction

noncomputable section

/-! Iterating derivations with one tangent-ideal factor per derivative. -/

variable (k : Type*) {R : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem relativeDifferential_weighted_step (A T H : Ideal R) (r : ℕ)
    (hA : A * T ^ r ≤ H) (hH : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k H * T ≤ H) :
    Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k A * T ^ (r + 1) ≤ H := by
  have hder : ∀ (D : Derivation k R R) (x : R), x ∈ A →
      ∀ y ∈ T ^ (r + 1), D x * y ∈ H := by
    intro D x hx y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      have hxa := hA (Ideal.mul_mem_mul hx ha)
      have h1 := hH (Ideal.mul_mem_mul
        (Relative.DifferentialBlowup.Construction.relative_derivation_mem_first k H D hxa) hb)
      have hDa : D a * b ∈ T ^ r := by
        cases r with
        | zero => simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
        | succ r =>
          rw [pow_succ]
          exact Ideal.mul_mem_mul (DifferentialOrder.Construction.derivation_mem_pow (D.restrictScalars ℤ) T r ha) hb
      have h2 := hA (Ideal.mul_mem_mul hx hDa)
      have h := H.sub_mem h1 h2
      convert h using 1
      rw [D.leibniz]
      change D x * (a * b) = (x * D a + a * D x) * b - x * (D a * b)
      ring
    · intro a b ha hb
      rw [mul_add]
      exact H.add_mem ha hb
  have hcolon : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k A ≤ H.colon (T ^ (r + 1) : Ideal R) := by
    apply sup_le
    · intro x hx
      apply Submodule.mem_colon.mpr
      intro y hy
      exact hA (Ideal.mul_mem_mul hx (Ideal.pow_le_pow_right (Nat.le_succ r) hy))
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟨D, p⟩, rfl⟩
      apply Submodule.mem_colon.mpr
      intro y hy
      exact hder D p.val p.property y hy
  apply Ideal.mul_le.mpr
  intro x hx y hy
  exact Submodule.mem_colon.mp (hcolon hx) y hy

/-- First-order tangent stability implies stability under every weighted
iterated differential ideal. -/
theorem iteratedRelativeDifferential_weighted_stability (H T : Ideal R)
    (hH : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k H * T ≤ H) (j : ℕ) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k H j * T ^ j ≤ H := by
  induction j with
  | zero => simp only [Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal, pow_zero, mul_one, le_refl]
  | succ j ih =>
    have h := relativeDifferential_weighted_step k
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k H j) T H j ih hH
    have he : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k H j) =
        Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k H (j + 1) := by
      simpa only [Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal] using
        (Relative.DifferentialProducts.Construction.iteratedRelativeDifferentialIdeal_add k H j 1).symm
    rw [he] at h
    exact h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.WeightedDifferentialStability.Construction
