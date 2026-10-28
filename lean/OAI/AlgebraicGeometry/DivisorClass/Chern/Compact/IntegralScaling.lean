import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.HolomorphicPeriod
import Mathlib.Data.Rat.Floor

/-! # Integral Scaling -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.IntegralScaling

noncomputable section

/-! Constructive common denominators for locally constant rational sections on compact sets. -/

open _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def rationalCommonDenominator (s : Finset ℚ) : ℕ := ∏ q ∈ s, q.den

theorem rationalCommonDenominator_pos (s : Finset ℚ) : 0 < rationalCommonDenominator s := by
  exact Finset.prod_pos (fun q _ => q.den_pos)

theorem rationalCommonDenominator_dvd (s : Finset ℚ) (q : ℚ) (hq : q ∈ s) :
    q.den ∣ rationalCommonDenominator s :=
  Finset.dvd_prod_of_mem (fun q : ℚ => q.den) hq

theorem rational_scaled_integer_of_den_dvd (q : ℚ) (N : ℕ) (h : q.den ∣ N) :
    ((((N / q.den : ℕ) : ℤ) * q.num : ℤ) : ℚ) = (N : ℚ) * q := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hn : ((N / q.den : ℕ) : ℚ) * q.den = (N : ℚ) := by
    exact_mod_cast Nat.div_mul_cancel h
  calc
    ((((N / q.den : ℕ) : ℤ) * q.num : ℤ) : ℚ) =
        ((N / q.den : ℕ) : ℚ) * (q.num : ℚ) := by push_cast; rfl
    _ = ((N / q.den : ℕ) : ℚ) * (q.den * q) := by
      congr 1
      simpa only [mul_comm] using (div_eq_iff hd).mp q.num_div_den
    _ = (N : ℚ) * q := by rw [← mul_assoc, hn]

/-- A locally constant rational section on a compact space has an explicitly constructed common denominator. -/
theorem locallyConstant_rat_clear_denominators {T : Type} [TopologicalSpace T] [CompactSpace T]
    (f : LocallyConstant T ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∃ g : LocallyConstant T ℤ, ∀ x, (g x : ℚ) = (N : ℚ) * f x := by
  classical
  let s := f.range_finite.toFinset
  let N := rationalCommonDenominator s
  refine ⟨N, rationalCommonDenominator_pos s,
    LocallyConstant.map (fun q : ℚ => ((N / q.den : ℕ) : ℤ) * q.num) f, ?_⟩
  intro x
  exact rational_scaled_integer_of_den_dvd (f x) N
    (rationalCommonDenominator_dvd s (f x) ((f.range_finite.mem_toFinset).mpr ⟨x, rfl⟩))

/-- The denominator is uniform on a compact subset of an arbitrary open domain. -/
theorem locallyConstant_rat_clear_denominators_on_compact {T : Type} [TopologicalSpace T]
    (U : Opens T) (f : LocallyConstant U ℚ) (K : Set T) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ N : ℕ, 0 < N ∧ ∃ g : LocallyConstant K ℤ,
      ∀ x : K, (g x : ℚ) = (N : ℚ) * f ⟨x.val, hKU x.property⟩ := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let fK : LocallyConstant K ℚ :=
    ⟨fun x => f ⟨x.val, hKU x.property⟩,
      f.isLocallyConstant.comp_continuous (continuous_subtype_val.subtype_mk _)⟩
  exact locallyConstant_rat_clear_denominators fK

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.IntegralScaling
