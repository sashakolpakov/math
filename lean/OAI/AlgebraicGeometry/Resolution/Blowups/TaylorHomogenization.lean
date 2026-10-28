import OAI.AlgebraicGeometry.Resolution.Blowups.NilpotentTaylorMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialEquiv

/-! # Taylor Homogenization -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TaylorHomogenization.Construction

noncomputable section

/-! Homogenization absorbs finite Taylor changes in tangent-ideal directions. -/

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem relative_derivation_pow_mem (D : Derivation k R R) (J : Ideal R)
    (j : ℕ) {x : R} (hx : x ∈ J) :
    (D.toLinearMap ^ j) x ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j := by
  induction j generalizing J x with
  | zero => exact hx
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply]
    exact ih (Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J) (Relative.DifferentialBlowup.Construction.relative_derivation_mem_first k J D hx)

variable {S : Type*} [CommRing S] [Algebra k S] [Algebra ℚ R] [Algebra ℚ S]

/-- Every Taylor term lies in the homogenization if the displacement lies in
the mapped tangent ideal. -/
theorem nilpotentTaylorMap_ideal_le_homogenized (D : Derivation k R R)
    (f : R →ₐ[k] S) (J : Ideal R) (t : S) (n : ℕ) (ht : t ^ (n + 1) = 0)
    (hT : t ∈ (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom) :
    J.map (NilpotentTaylorMap.Construction.nilpotentTaylorMap D f t (n + 1) ht).toRingHom ≤
      (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  change NilpotentTaylorMap.Construction.nilpotentTaylorMap D f t (n + 1) ht x ∈
    (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom
  rw [NilpotentTaylorMap.Construction.nilpotentTaylorMap_apply]
  apply Ideal.sum_mem
  intro j hj
  have hjn : j < n + 1 := Finset.mem_range.mp hj
  have hpart : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j *
      (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) ^ j ≤ Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n := by
    unfold Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal
    exact le_iSup_of_le ⟨j, hjn⟩ le_rfl
  have hmap : (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j).map f.toRingHom *
      ((Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map f.toRingHom) ^ j ≤
        (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n).map f.toRingHom := by
    rw [← Ideal.map_pow, ← Ideal.map_mul]
    exact Ideal.map_mono hpart
  have hp := Ideal.mem_map_of_mem f.toRingHom (relative_derivation_pow_mem D J j hx)
  have hprod := hmap (Ideal.mul_mem_mul hp (Ideal.pow_mem_pow hT j))
  rw [mul_comm] at hprod
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ hprod

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TaylorHomogenization.Construction
