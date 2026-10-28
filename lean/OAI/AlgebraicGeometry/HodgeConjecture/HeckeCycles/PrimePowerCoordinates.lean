import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TorsionCoordinateMaps

/-! # Prime Power Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimePowerCoordinates.CM

/-! The first torsion subgroup of a power-level cyclic coordinate
consists exactly of the top-power multiples of first-level residues. -/

theorem first_torsion_value_divisible (q n : ℕ) (hq : 0 < q)
    (x : ZMod (q ^ (n + 1))) (hx : q • x = 0) : q ^ n ∣ x.val := by
  let : NeZero (q ^ (n + 1)) := ⟨pow_ne_zero _ hq.ne'⟩
  have hz : ((q * x.val : ℕ) : ZMod (q ^ (n + 1))) = 0 := by
    simpa only [Nat.cast_mul, ZMod.natCast_zmod_val, nsmul_eq_mul] using hx
  have hd := (ZMod.natCast_eq_zero_iff (q * x.val) (q ^ (n + 1))).mp hz
  exact (Nat.mul_dvd_mul_iff_left hq).mp
    ((congrArg (fun d : ℕ => d ∣ q * x.val) (pow_succ' q n)).mp hd)

theorem first_torsion_coordinates (q n : ℕ) (hq : 0 < q)
    (x : ZMod (q ^ (n + 1))) (hx : q • x = 0) :
    ∃ r : Fin q, x = (q ^ n : ZMod (q ^ (n + 1))) * (r.val : ZMod (q ^ (n + 1))) := by
  let : NeZero (q ^ (n + 1)) := ⟨pow_ne_zero _ hq.ne'⟩
  have hd := first_torsion_value_divisible q n hq x hx
  have hr : x.val / q ^ n < q := by
    apply (Nat.div_lt_iff_lt_mul (pow_pos hq n)).mpr
    simpa only [← pow_succ'] using x.val_lt
  refine ⟨⟨x.val / q ^ n, hr⟩, ?_⟩
  calc
    x = (x.val : ZMod (q ^ (n + 1))) := x.natCast_zmod_val.symm
    _ = ((q ^ n * (x.val / q ^ n) : ℕ) : ZMod (q ^ (n + 1))) :=
      congrArg (fun t : ℕ => (t : ZMod (q ^ (n + 1)))) (Nat.mul_div_cancel' hd).symm
    _ = _ := by rw [Nat.cast_mul, Nat.cast_pow]

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrimePowerCoordinates.CM
