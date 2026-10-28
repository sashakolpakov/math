import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterUniqueness

/-! # Projective Invariants -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectiveInvariants.Central

noncomputable section

/-! Three degree-zero symmetric expressions determine a nonzero triple
up to a common scalar and permutation, including vanishing sums and
repeated entries. -/

theorem cubic_pair_scale {F : Type*} [Field F] (x y a b : F)
    (hx : x ^ 3 = a ^ 3) (hy : y ^ 3 = b ^ 3) (hxy : x * y = a * b) :
    ∃ z : F, z ^ 3 = 1 ∧ x = z * a ∧ y = z ^ 2 * b := by
  by_cases ha : a = 0
  · have hzero : x = 0 := by simpa [ha] using hx
    by_cases hb : b = 0
    · have hyzero : y = 0 := by simpa [hb] using hy
      exact ⟨1, by simp, by simp [ha, hzero], by simp [hb, hyzero]⟩
    · let r := y / b
      have hr : r ^ 3 = 1 := by dsimp [r]; rw [div_pow, hy, div_self (pow_ne_zero _ hb)]
      refine ⟨r ^ 2, ?_, by simp [ha, hzero], ?_⟩
      · calc (r ^ 2) ^ 3 = (r ^ 3) ^ 2 := by ring
             _ = 1 := by rw [hr, one_pow]
      · calc y = r * b := (div_mul_cancel₀ y hb).symm
             _ = (r ^ 2) ^ 2 * b := by
               rw [show (r ^ 2) ^ 2 = r ^ 3 * r by ring, hr, one_mul]
  · let r := x / a
    have hr : r ^ 3 = 1 := by dsimp [r]; rw [div_pow, hx, div_self (pow_ne_zero _ ha)]
    have hxa : r * a = x := div_mul_cancel₀ x ha
    have hyr : r * y = b := by
      apply mul_left_cancel₀ ha
      calc a * (r * y) = (r * a) * y := by ring
           _ = x * y := by rw [hxa]
           _ = a * b := hxy
    refine ⟨r, hr, hxa.symm, ?_⟩
    calc y = r ^ 3 * y := by rw [hr, one_mul]
         _ = r ^ 2 * (r * y) := by ring
         _ = r ^ 2 * b := by rw [hyr]

theorem projective_triple_of_invariants {F : Type*} [Field F] [IsAlgClosed F]
    (α β : Fin 3 → F)
    (ha : α 0 * α 1 * α 2 ≠ 0) (hb : β 0 * β 1 * β 2 ≠ 0)
    (hs : (α 0 + α 1 + α 2) ^ 3 * (β 0 * β 1 * β 2) =
      (β 0 + β 1 + β 2) ^ 3 * (α 0 * α 1 * α 2))
    (hp : (α 0 * α 1 + α 0 * α 2 + α 1 * α 2) ^ 3 * (β 0 * β 1 * β 2) ^ 2 =
      (β 0 * β 1 + β 0 * β 2 + β 1 * β 2) ^ 3 * (α 0 * α 1 * α 2) ^ 2)
    (hm : (α 0 + α 1 + α 2) * (α 0 * α 1 + α 0 * α 2 + α 1 * α 2) * (β 0 * β 1 * β 2) =
      (β 0 + β 1 + β 2) * (β 0 * β 1 + β 0 * β 2 + β 1 * β 2) * (α 0 * α 1 * α 2)) :
    ∃ c : F, c ≠ 0 ∧ ∃ σ : Equiv.Perm (Fin 3), ∀ i, α i = c * β (σ i) := by
  let sa := α 0 + α 1 + α 2
  let sb := β 0 + β 1 + β 2
  let pa := α 0 * α 1 + α 0 * α 2 + α 1 * α 2
  let pb := β 0 * β 1 + β 0 * β 2 + β 1 * β 2
  let da := α 0 * α 1 * α 2
  let db := β 0 * β 1 * β 2
  change sa ^ 3 * db = sb ^ 3 * da at hs
  change pa ^ 3 * db ^ 2 = pb ^ 3 * da ^ 2 at hp
  change sa * pa * db = sb * pb * da at hm
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (da / db) (by norm_num : 0 < 3)
  have hcprod : c ^ 3 * db = da := (eq_div_iff hb).mp hc
  have hc0 : c ≠ 0 := by
    intro hz
    apply ha
    simpa only [hz, zero_pow (by norm_num : 3 ≠ 0), zero_mul] using hcprod.symm
  have hs' : sa ^ 3 = (c * sb) ^ 3 := by
    apply mul_right_cancel₀ hb
    linear_combination hs - sb ^ 3 * hcprod
  have hc2 : c ^ 6 * db ^ 2 = da ^ 2 := by
    calc c ^ 6 * db ^ 2 = (c ^ 3 * db) ^ 2 := by ring
         _ = da ^ 2 := by rw [hcprod]
  have hp' : pa ^ 3 = (c ^ 2 * pb) ^ 3 := by
    apply mul_right_cancel₀ (pow_ne_zero 2 hb)
    linear_combination hp - pb ^ 3 * hc2
  have hm' : sa * pa = (c * sb) * (c ^ 2 * pb) := by
    apply mul_right_cancel₀ hb
    linear_combination hm - (sb * pb) * hcprod
  obtain ⟨z, hz, hsz, hpz⟩ := cubic_pair_scale sa pa (c * sb) (c ^ 2 * pb) hs' hp' hm'
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  refine ⟨z * c, mul_ne_zero hz0 hc0, ?_⟩
  apply ParameterUniqueness.Central.parameter_triple_unique α (fun i => (z * c) * β i)
  · change sa = z * c * β 0 + z * c * β 1 + z * c * β 2
    rw [hsz]
    dsimp [sb]
    ring
  · change pa = (z * c * β 0) * (z * c * β 1) +
      (z * c * β 0) * (z * c * β 2) + (z * c * β 1) * (z * c * β 2)
    rw [hpz]
    dsimp [pb]
    ring
  · change da = (z * c * β 0) * (z * c * β 1) * (z * c * β 2)
    calc da = z ^ 3 * (c ^ 3 * db) := by rw [hz, one_mul, hcprod]
         _ = _ := by dsimp [db]; ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectiveInvariants.Central
