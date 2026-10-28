import OAI.RepresentationTheory.Weil.Local.SquareIndexTools

/-! # Index Two Phase Character -/

namespace OAI.RepresentationTheory.Weil.Local.IndexTwoPhaseCharacter.Construction

noncomputable section

/-! A phase invariant on index-two norm classes yields a quadratic character after normalization. -/

variable {G C : Type*} [CommGroup G] [CommGroup C]
  (N : Subgroup G) (hN : N.index = 2) (r : G → C) (j : G)
  (hi : ∀ a b : G, b ∈ N → r (a * b) = r a)
  (hj : ∀ a : G, r (j * a) = (r a)⁻¹) (hfour : ∀ a : G, r a ^ 4 = 1)

include hi in
omit [CommGroup C] in
theorem normClass_phase_eq {a b : G} (hab : a⁻¹ * b ∈ N) : r a = r b := by
  have hh := hi a (a⁻¹ * b) hab
  simpa only [mul_inv_cancel_left] using hh.symm

include hN hi hj hfour

theorem indexTwo_phase_ratio_square (a : G) : (r a / r 1) ^ 2 = 1 := by
  have hmem (b : G) (hb : b ∈ N) : r b = r 1 := by simpa only [one_mul] using hi 1 b hb
  by_cases hjN : j ∈ N
  · have hs (b : G) : r b ^ 2 = 1 := by
      have he : r b = (r b)⁻¹ := by
        have hh := hi b j hjN
        rw [mul_comm b j, hj] at hh
        exact hh.symm
      calc
        r b ^ 2 = r b * r b := pow_two _
        _ = r b * (r b)⁻¹ := congrArg (fun x => r b * x) he
        _ = 1 := mul_inv_cancel _
    rw [div_pow, hs a, hs 1, div_self']
  · by_cases haN : a ∈ N
    · rw [hmem a haN, div_self', one_pow]
    · have hja : j⁻¹ * a ∈ N := (N.mul_mem_iff_of_index_two hN).mpr
        (iff_of_false (by simpa only [N.inv_mem_iff] using hjN) haN)
      have he : r a = r j := (normClass_phase_eq N r hi hja).symm
      have hj1 : r j = (r 1)⁻¹ := by simpa only [mul_one] using hj 1
      rw [he, hj1, div_pow, inv_pow, div_eq_mul_inv, ← mul_inv, ← pow_add]
      change (r 1 ^ 4)⁻¹ = 1
      rw [hfour, inv_one]

theorem indexTwo_phase_ratio_mul (a b : G) :
    r (a * b) / r 1 = (r a / r 1) * (r b / r 1) := by
  let F := fun x => r x / r 1
  have hmem (x : G) (hx : x ∈ N) : F x = 1 := by
    have hh : r x = r 1 := by simpa only [one_mul] using hi 1 x hx
    dsimp only [F]
    rw [hh, div_self']
  have hmul (x y : G) (hy : y ∈ N) : F (x * y) = F x := by
    dsimp only [F]
    rw [hi x y hy]
  change F (a * b) = F a * F b
  by_cases ha : a ∈ N
  · rw [mul_comm a b, hmul b a ha, hmem a ha, one_mul]
  by_cases hb : b ∈ N
  · rw [hmul a b hb, hmem b hb, mul_one]
  have hab : a * b ∈ N := (N.mul_mem_iff_of_index_two hN).mpr (iff_of_false ha hb)
  have hab' : a⁻¹ * b ∈ N := (N.mul_mem_iff_of_index_two hN).mpr
    (iff_of_false (by simpa only [N.inv_mem_iff] using ha) hb)
  have he : F b = F a := congrArg (fun x => x / r 1) (normClass_phase_eq N r hi hab').symm
  rw [hmem (a * b) hab, he, ← pow_two]
  exact (indexTwo_phase_ratio_square N hN r j hi hj hfour a).symm

def indexTwoPhaseCharacter : G →* C where
  toFun a := r a / r 1
  map_one' := div_self' _
  map_mul' := indexTwo_phase_ratio_mul N hN r j hi hj hfour

end

end OAI.RepresentationTheory.Weil.Local.IndexTwoPhaseCharacter.Construction
