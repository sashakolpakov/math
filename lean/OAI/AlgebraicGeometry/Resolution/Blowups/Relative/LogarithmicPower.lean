import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.AuxiliaryIdeal
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.TransverseHypersurfaceCoordinates

/-! # Logarithmic Power -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicPower.Construction

noncomputable section

/-! Coordinate powers supply relative logarithmic bounds for the old-boundary auxiliary ideals. -/

section

variable (k : Type*) {R ι : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem iterated_relative_logarithmic_derivation_mem (w : ι → R)
    (D : LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) (J : Ideal R) (p : R) (hp : p ∈ J) (n : ℕ) :
    D.val^[n] p ∈ LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J n := by
  induction n generalizing J p with
  | zero => exact hp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (LogarithmicIdeal.Construction.firstRelativeLogarithmicDifferentialIdeal k w J) (D.val p)
      (LogarithmicIdeal.Construction.relative_logarithmic_derivation_mem_first k w J D hp)

theorem relative_logarithmic_bound_of_coordinate_power [Algebra ℚ R]
    (w : ι → R) (D : LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) (z : R) (hz : D.val z = 1)
    (J : Ideal R) (m : ℕ) (hzm : z ^ m ∈ J) :
    LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J m = ⊤ := by
  have hfact := iterated_relative_logarithmic_derivation_mem k w D J (z ^ m) hzm m
  change (D.val.restrictScalars ℤ)^[m] (z ^ m) ∈ _ at hfact
  rw [LogarithmicCoordinatePower.Construction.iteratedRingDerivation_coordinate_power (D.val.restrictScalars ℤ) z hz m] at hfact
  exact Ideal.eq_top_of_isUnit_mem _ hfact (DerivativeHypersurfacePersistence.Construction.factorial_isUnit_of_rationalAlgebra m)

theorem coordinate_mem_relative_logarithmic_of_power [Algebra ℚ R]
    (w : ι → R) (D : LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) (z : R) (hz : D.val z = 1)
    (J : Ideal R) (m : ℕ) (hzm : z ^ (m + 1) ∈ J) :
    z ∈ LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal k w J m := by
  have hfact := iterated_relative_logarithmic_derivation_mem k w D J (z ^ (m + 1)) hzm m
  change (D.val.restrictScalars ℤ)^[m] (z ^ (m + 1)) ∈ _ at hfact
  rw [LogarithmicCoordinatePower.Construction.iteratedRingDerivation_penultimate_power (D.val.restrictScalars ℤ) z hz m] at hfact
  exact (Ideal.unit_mul_mem_iff_mem _ (DerivativeHypersurfacePersistence.Construction.factorial_isUnit_of_rationalAlgebra (m + 1))).mp hfact

end

universe u

variable {σ K S : Type u} [Field K] [CharZero K] [CommRing S] [DecidableEq σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]
  [Algebra K S] [IsScalarTower K (MvPolynomial σ K) S]

/-- The old-boundary auxiliary ideal has its explicit coordinate equation in
the relative logarithmic and homogenization tangent ideals, with the relative
unit bound at the same control. -/
theorem etale_boundary_auxiliary_relative_logarithmic_equation
    (B L : Finset σ) (h : σ) (hhB : h ∈ B) (hhL : h ∉ L) (J : Ideal S) (m : ℕ) :
    let w := fun j : L => algebraMap (MvPolynomial σ K) S (MvPolynomial.X j.val)
    let H := Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) B) (m + 1)
    LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal K w H (m + 1) = ⊤ ∧
      algebraMap (MvPolynomial σ K) S (MvPolynomial.X h) ∈
        LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal K w H m ∧
      algebraMap (MvPolynomial σ K) S (MvPolynomial.X h) ∈
        DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal K H m := by
  let : Algebra ℚ S := ((algebraMap K S).comp (algebraMap ℚ K)).toAlgebra
  let w := fun j : L => algebraMap (MvPolynomial σ K) S (MvPolynomial.X j.val)
  let z := algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)
  let H := Boundary.AuxiliaryIdeal.Construction.boundaryAuxiliaryIdeal J (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := K) (S := S) B) (m + 1)
  let D : LogarithmicIdeal.Construction.relativeLogarithmicDerivations K w := ⟨Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) h, by
    intro j
    have hhj : h ≠ j.val := fun he => hhL (he.symm ▸ j.property)
    change Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) h
      (algebraMap (MvPolynomial σ K) S (MvPolynomial.X j.val)) ∈ Ideal.span {w j}
    rw [Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X, ite_eq_right hhj]
    exact Ideal.zero_mem _⟩
  have hDz : D.val z = 1 := by
    change Blowups.Etale.DifferentialEquation.Construction.etaleRelativePartial (K := K) (S := S) h
      (algebraMap (MvPolynomial σ K) S (MvPolynomial.X h)) = 1
    rw [Blowups.Etale.TransverseHypersurfaceCoordinates.Construction.etaleRelativePartial_X, ite_eq_left rfl]
  have hzm : z ^ (m + 1) ∈ H := Submodule.mem_sup_right
    (Ideal.pow_mem_pow (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement (K := K) (S := S) B ⟨h, hhB⟩).property (m + 1))
  have hmem := coordinate_mem_relative_logarithmic_of_power K w D z hDz H m hzm
  exact ⟨relative_logarithmic_bound_of_coordinate_power K w D z hDz H (m + 1) hzm, hmem,
    LogarithmicIdeal.Construction.iteratedRelativeLogarithmicDifferentialIdeal_le_relative K w H m hmem⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.LogarithmicPower.Construction
