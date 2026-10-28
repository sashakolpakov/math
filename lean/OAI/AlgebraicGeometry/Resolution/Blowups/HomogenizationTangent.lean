import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialEquiv
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialProducts

/-! # Homogenization Tangent -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizationTangent.Construction

noncomputable section

/-! Homogenization preserves the intrinsic tangent ideal exactly. -/

variable (k : Type*) {R : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem relativeHomogenizedIdeal_component (J : Ideal R) (n j : ℕ) (hj : j ≤ n) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j *
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) ^ j ≤ Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n := by
  unfold Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal
  exact le_iSup_of_le ⟨j, Nat.lt_succ_of_le hj⟩ le_rfl

/-- The tangent ideal is unchanged by homogenization, including its full
scheme structure. -/
theorem relativeHomogenizedIdeal_tangent (J : Ideal R) (n : ℕ) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) n =
      Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n := by
  apply le_antisymm
  · unfold Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal
    rw [Relative.DifferentialProducts.Construction.iteratedRelativeDifferentialIdeal_iSup]
    apply iSup_le
    intro j
    have hj : j.val ≤ n := Nat.le_of_lt_succ j.isLt
    have hJ : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
        (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val) (n - j.val) ≤
          Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n := by
      rw [← Relative.DifferentialProducts.Construction.iteratedRelativeDifferentialIdeal_add, Nat.add_sub_of_le hj]
    have h := Relative.DifferentialProducts.Construction.relativeDifferential_product_power_bound k
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val)
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) (n - j.val) j.val hJ
    simpa only [Nat.sub_add_cancel hj] using h
  · exact Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_mono k n (Relative.DifferentialEquiv.Construction.le_relativeHomogenizedIdeal k J n)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizationTangent.Construction
