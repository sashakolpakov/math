import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MixedPowerFiniteDifferences

/-! # Integer Mixed Power Differences -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegerMixedPowerDifferences

noncomputable section

/-! The mixed power-difference coefficient holds integrally. Casts
and restriction to integer arguments commute with every difference. -/

theorem fwdDiff_iter_int_restrict (f : ℚ → ℚ) (d : ℤ) (n : ℕ) (z : ℤ) :
    (fwdDiff d)^[n] (fun w : ℤ => f (w : ℚ)) z =
      (fwdDiff (d : ℚ))^[n] f (z : ℚ) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (fwdDiff d)^[n] (fun w : ℤ => f (w : ℚ)) (z + d) -
        (fwdDiff d)^[n] (fun w : ℤ => f (w : ℚ)) z =
      (fwdDiff (d : ℚ))^[n] f ((z : ℚ) + d) - (fwdDiff (d : ℚ))^[n] f (z : ℚ)
    rw [ih, ih, Int.cast_add]

theorem fwdDiff_iter_int_cast (f : ℤ → ℤ) (d : ℤ) (n : ℕ) (z : ℤ) :
    (fwdDiff d)^[n] (fun w : ℤ => (f w : ℚ)) z = (((fwdDiff d)^[n] f z : ℤ) : ℚ) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (fwdDiff d)^[n] (fun w : ℤ => (f w : ℚ)) (z + d) -
        (fwdDiff d)^[n] (fun w : ℤ => (f w : ℚ)) z =
      (((fwdDiff d)^[n] f (z + d) - (fwdDiff d)^[n] f z : ℤ) : ℚ)
    rw [ih, ih, Int.cast_sub]

theorem integer_mixedPower_finiteDifference (g : ℕ) (d : ℤ) (hd : d ≠ 0) (z : ℤ) :
    fwdDiff 1 ((fwdDiff d)^[g] (fun w : ℤ => w ^ (g + 1))) z =
      ((g + 1).factorial : ℤ) * d ^ g := by
  apply Int.cast_injective (α := ℚ)
  have hcast : ((fwdDiff 1 ((fwdDiff d)^[g] (fun w : ℤ => w ^ (g + 1))) z : ℤ) : ℚ) =
      fwdDiff 1 ((fwdDiff (d : ℚ))^[g] (fun w : ℚ => w ^ (g + 1))) (z : ℚ) := by
    change (((fwdDiff d)^[g] (fun w : ℤ => w ^ (g + 1)) (z + 1) -
        (fwdDiff d)^[g] (fun w : ℤ => w ^ (g + 1)) z : ℤ) : ℚ) = _
    rw [Int.cast_sub, ← fwdDiff_iter_int_cast, ← fwdDiff_iter_int_cast]
    have he : (fun w : ℤ => ((w ^ (g + 1) : ℤ) : ℚ)) =
        (fun w : ℤ => (w : ℚ) ^ (g + 1)) := by funext w; exact Int.cast_pow w _
    rw [he, fwdDiff_iter_int_restrict (fun w : ℚ => w ^ (g + 1)) d g (z + 1),
      fwdDiff_iter_int_restrict (fun w : ℚ => w ^ (g + 1)) d g z, Int.cast_add, Int.cast_one]
    rfl
  rw [hcast, MixedPowerFiniteDifferences.mixedPower_finiteDifference g (d : ℚ) (by exact_mod_cast hd)]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_natCast]

theorem integer_mixedMonomial_finiteDifference (g : ℕ) (c d z : ℤ) (hd : d ≠ 0) :
    fwdDiff 1 ((fwdDiff d)^[g] (fun w : ℤ => c * w ^ (g + 1))) z =
      c * ((g + 1).factorial : ℤ) * d ^ g := by
  change fwdDiff 1 ((fwdDiff d)^[g] (c • (fun w : ℤ => w ^ (g + 1)))) z = _
  rw [fwdDiff_iter_const_smul, fwdDiff_const_smul]
  change c * fwdDiff 1 ((fwdDiff d)^[g] (fun w : ℤ => w ^ (g + 1))) z = _
  rw [integer_mixedPower_finiteDifference g d hd z, mul_assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegerMixedPowerDifferences
