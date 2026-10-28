import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledTransform

/-! # Differential Equiv -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialEquiv.Construction

noncomputable section

section

/-! Relative homogenization of a marked ideal, for comparing maximal-contact choices. -/

variable (k : Type*) {R : Type*} [CommRing k] [CommRing R] [Algebra k R]

/-- Homogenization at control `n+1`, using the intrinsic relative
control-one tangent ideal `Δⁿ(J)`. -/
def relativeHomogenizedIdeal (J : Ideal R) (n : ℕ) : Ideal R :=
  ⨆ j : Fin (n + 1), DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val *
    (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) ^ j.val

theorem le_relativeHomogenizedIdeal (J : Ideal R) (n : ℕ) :
    J ≤ relativeHomogenizedIdeal k J n := by
  unfold relativeHomogenizedIdeal
  have h := le_iSup (fun j : Fin (n + 1) => DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val *
    (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) ^ j.val) ⟨0, Nat.zero_lt_succ n⟩
  simpa only [DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal, pow_zero, mul_one] using h

/-- The homogenized ideal contains the full control power of the
tangent ideal. This is the term that absorbs Taylor remainders. -/
theorem tangentIdeal_power_le_relativeHomogenizedIdeal (J : Ideal R) (n : ℕ) :
    (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) ^ (n + 1) ≤ relativeHomogenizedIdeal k J n := by
  unfold relativeHomogenizedIdeal
  have h := le_iSup (fun j : Fin (n + 1) => DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val *
    (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) ^ j.val) ⟨n, Nat.lt_succ_self n⟩
  simpa only [pow_succ'] using h

/-- Homogenization preserves the full permissible-center test, for
every ideal, rather than only the set of closed high-order points. -/
theorem relativeHomogenizedIdeal_permissible_iff (I J : Ideal R) (n : ℕ) :
    relativeHomogenizedIdeal k J n ≤ I ^ (n + 1) ↔ J ≤ I ^ (n + 1) := by
  constructor
  · intro h
    exact (le_relativeHomogenizedIdeal k J n).trans h
  · intro hJ
    have hT : DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n ≤ I := by
      have h := (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k J n).trans
        (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow I J 1 n (by simpa only [Nat.add_comm 1 n] using hJ))
      simpa only [pow_one] using h
    apply iSup_le
    intro j
    have hD : DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J j.val ≤ I ^ (n + 1 - j.val) :=
      (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k J j.val).trans
        (DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow I J (n + 1 - j.val) j.val
          (by simpa only [Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using hJ))
    have hprod := Ideal.mul_mono hD (pow_le_pow_left' hT j.val)
    simpa only [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt j.isLt)] using hprod

/-- Every ideal lying between an ideal and its homogenization has the
same marked center conditions. -/
theorem relative_homogenized_interval_permissible_iff
    (I J L : Ideal R) (n : ℕ) (hJL : J ≤ L) (hLH : L ≤ relativeHomogenizedIdeal k J n) :
    L ≤ I ^ (n + 1) ↔ J ≤ I ^ (n + 1) := by
  constructor
  · exact hJL.trans
  · intro hJ
    exact hLH.trans ((relativeHomogenizedIdeal_permissible_iff k I J n).mpr hJ)

end

/-! Intrinsic differential ideals and homogenization respect algebra isomorphisms. -/

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

def transportRelativeDerivation (e : R ≃ₐ[k] S) (D : Derivation k R R) : Derivation k S S where
  toLinearMap := e.toLinearMap.comp (D.toLinearMap.comp e.symm.toLinearMap)
  map_one_eq_zero' := by
    change e (D (e.symm 1)) = 0
    rw [map_one, D.map_one_eq_zero, map_zero]
  leibniz' x y := by
    change e (D (e.symm (x * y))) = x * e (D (e.symm y)) + y * e (D (e.symm x))
    rw [map_mul, D.leibniz]
    change e (e.symm x * D (e.symm y) + e.symm y * D (e.symm x)) = _
    rw [map_add, map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply]

theorem transportRelativeDerivation_apply (e : R ≃ₐ[k] S) (D : Derivation k R R) (x : S) :
    transportRelativeDerivation e D x = e (D (e.symm x)) := rfl

theorem transportRelativeDerivation_map (e : R ≃ₐ[k] S) (D : Derivation k R R) (x : R) :
    transportRelativeDerivation e D (e x) = e (D x) := by
  rw [transportRelativeDerivation_apply, e.symm_apply_apply]

theorem firstRelativeDifferentialIdeal_map_equiv (e : R ≃ₐ[k] S) (J : Ideal R) :
    (DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J).map e.toRingHom =
      DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (J.map e.toRingHom) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    apply sup_le
    · intro x hx
      exact DifferentialBlowup.Construction.le_firstRelativeDifferentialIdeal k (J.map e.toRingHom)
        (Ideal.mem_map_of_mem e.toRingHom hx)
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟨D, p⟩, rfl⟩
      have h := DifferentialBlowup.Construction.relative_derivation_mem_first k (J.map e.toRingHom)
        (transportRelativeDerivation e D) (Ideal.mem_map_of_mem e.toRingHom p.property)
      change transportRelativeDerivation e D (e p.val) ∈
        DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (J.map e.toRingHom) at h
      rw [transportRelativeDerivation_map] at h
      exact h
  · apply sup_le
    · exact Ideal.map_mono (DifferentialBlowup.Construction.le_firstRelativeDifferentialIdeal k J)
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟨D, q⟩, rfl⟩
      obtain ⟨p, hp, hpq⟩ :=
        (Ideal.mem_map_iff_of_surjective e.toRingHom e.surjective).mp q.property
      change D q.val ∈ (DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J).map e.toRingHom
      rw [← hpq]
      have h := Ideal.mem_map_of_mem e.toRingHom
        (DifferentialBlowup.Construction.relative_derivation_mem_first k J (transportRelativeDerivation e.symm D) hp)
      change e (e.symm (D (e p))) ∈ (DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J).map e.toRingHom at h
      rw [e.apply_symm_apply] at h
      exact h

theorem iteratedRelativeDifferentialIdeal_map_equiv (e : R ≃ₐ[k] S)
    (J : Ideal R) (n : ℕ) :
    (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n).map e.toRingHom =
      DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map e.toRingHom) n := by
  induction n generalizing J with
  | zero => rfl
  | succ n ih =>
    simp only [DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal]
    rw [ih, firstRelativeDifferentialIdeal_map_equiv]

theorem relativeHomogenizedIdeal_map_equiv (e : R ≃ₐ[k] S) (J : Ideal R) (n : ℕ) :
    (relativeHomogenizedIdeal k J n).map e.toRingHom =
      relativeHomogenizedIdeal k (J.map e.toRingHom) n := by
  unfold relativeHomogenizedIdeal
  simp only [Ideal.map_iSup, Ideal.map_mul, Ideal.map_pow,
    iteratedRelativeDifferentialIdeal_map_equiv]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialEquiv.Construction
