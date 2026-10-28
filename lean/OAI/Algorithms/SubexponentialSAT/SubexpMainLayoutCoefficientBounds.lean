import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutWordBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutChoicesTrace
import OAI.Algorithms.SubexponentialSAT.SubexpCoefficientBounds

namespace OAI.Algorithms

/-!
# Measured bounds for the coefficient and scalar-cache stages of Main layout

The incoming bound selects only layout storage and the retained parameter
words. The pending leaf stream is not selected. The coefficient search keeps
its actual `p^R` enumeration factor. Its output stacks are not read by the
following scalar-cache stages, so their bounds use the coefficient result's
proved frame and cleanup rather than an assumed intermediate size bound.
-/

namespace SubexponentialSAT.SubexpMainLayoutCoefficientBounds

open BitProgram StructuredCalls SubexpMainProgram Subexp
open SubexpMainLayoutWordBounds
open SubexpLayoutPorts (Allocation master ordinary)
open scoped BigOperators

attribute [local simp] Fin.coe_ofNat_eq_mod

def coefficientBound (W p Q R : ℕ) : ℕ :=
  22000000000 * (64 * W + p + Q + R + MatrixWordEncoding.width p + 2)^7 * p^R

def scalarBound (W p : ℕ) : ℕ :=
  500 * (14 * W + p + 1) * (MatrixWordEncoding.width p + 1)

def frameWidthBound (W p : ℕ) : ℕ :=
  7 * (2 * MatrixWordEncoding.width p + 1) + 4 * W + 16

def bound (W p Q R : ℕ) : ℕ :=
  coefficientBound W p Q R + scalarBound W p + frameWidthBound W p

theorem coefficient_relevant {es : ℕ} (alloc : Allocation es) (i : Fin 64) :
    RelevantPort es (SubexpMainCoefficients.stackMap alloc i) := by
  unfold SubexpMainCoefficients.stackMap
  split_ifs
  · exact Or.inr ⟨6, rfl, Or.inl (by unfold SubexpMainInvariant.ParameterPort; decide)⟩
  · exact Or.inr ⟨21, rfl, Or.inl (by unfold SubexpMainInvariant.ParameterPort; decide)⟩
  · exact Or.inr ⟨17, rfl, Or.inl (by unfold SubexpMainInvariant.ParameterPort; decide)⟩
  · exact Or.inr ⟨25, rfl, Or.inl (by unfold SubexpMainInvariant.ParameterPort; decide)⟩
  · exact Or.inl (by change 649 < 672; decide)
  · exact Or.inl (by change 254 < 672; decide)
  · apply Or.inl
    change i.val < 672
    omega

/-- The selected size is the sum of exactly the 64 physically selected words. -/
theorem selectedSize_le {er es W : ℕ} (alloc : Allocation es)
    {a : MainState er es} (h : RelevantWordBound W a) :
    SubexpMainLayoutChoices.selectedSize alloc a ≤ 64 * W := by
  exact sum_lengths h (SubexpMainCoefficients.stackMap alloc) (coefficient_relevant alloc)

theorem coefficient_budget_le {er es W p r Q R : ℕ} [Fact p.Prime]
    (alloc : Allocation es) {a : MainState er es} (h : RelevantWordBound W a) :
    SubexpCoefficientProgram.budget p r Q R
      (SubexpMainLayoutChoices.selectedSize alloc a) ≤ coefficientBound W p Q R := by
  have hs := selectedSize_le alloc h
  calc
    _ ≤ 22000000000 *
        (SubexpMainLayoutChoices.selectedSize alloc a + p + Q + R +
          MatrixWordEncoding.width p + 2)^7 * p^R :=
      SubexpCoefficientBounds.budget_le_polynomial_times_power _ _ _ _ _
    _ ≤ coefficientBound W p Q R := by
      unfold coefficientBound
      gcongr

/-- Every selected word except the two coefficient outputs is still bounded
by the incoming bound. The low work bank is physically empty. -/
theorem coefficient_frame_le {er es W p r Q R : ℕ} [Fact p.Prime]
    (alloc : Allocation es) {a b : MainState er es} (h : RelevantWordBound W a)
    (hc : SubexpMainCoefficients.Result alloc a b p r Q R)
    (i : Fin (totalStacks es)) (hi : RelevantPort es i)
    (hout : i ≠ master alloc 9) (hcopy : i ≠ ordinary alloc 254) :
    (b.stacks i).length ≤ W := by
  by_cases hs : i.val < 64
  · have he : SubexpMainCoefficients.low alloc ⟨i.val, hs⟩ = i := Fin.ext rfl
    rw [← he, hc.scratch]
    exact Nat.zero_le W
  · rw [hc.frame i (by omega) hout hcopy]
    exact h i hi

theorem scalar_relevant {es : ℕ} (alloc : Allocation es) (i : Fin 14) :
    RelevantPort es (SubexpMainScalarAlphabet.stackMap alloc i) := by
  by_cases hz : i.val = 0
  · have he : i = 0 := Fin.ext hz
    subst i
    exact Or.inr ⟨6, rfl, Or.inl (by unfold SubexpMainInvariant.ParameterPort; decide)⟩
  · apply Or.inl
    rw [SubexpMainScalarAlphabet.stackMap_value, ite_eq_right hz]
    split_ifs <;> omega

private theorem scalar_ne_outputs {es : ℕ} (alloc : Allocation es) (i : Fin 14) :
    SubexpMainScalarAlphabet.stackMap alloc i ≠ master alloc 9 ∧
      SubexpMainScalarAlphabet.stackMap alloc i ≠ ordinary alloc 254 := by
  have hw := alloc.enough.trans alloc.within
  constructor <;> intro he
  all_goals
    have hv := congrArg (fun j : Fin (totalStacks es) => j.val) he
    change (SubexpMainScalarAlphabet.stackMap alloc i).val = _ at hv
    rw [SubexpMainScalarAlphabet.stackMap_value] at hv
    split_ifs at hv <;> norm_num only [SubexpLayoutPorts.master_val,
      SubexpLayoutPorts.ordinary, Fin.val_mk, Fin.coe_ofNat_eq_mod] at hv <;> omega

theorem scalar_selectedSize_le {er es W p r Q R : ℕ} [Fact p.Prime]
    (alloc : Allocation es) {a b : MainState er es} (h : RelevantWordBound W a)
    (hc : SubexpMainCoefficients.Result alloc a b p r Q R) :
    stackBits ((SubexpMainScalarAlphabet.procedure er alloc).project b).stacks ≤ 14 * W := by
  change (∑ i : Fin 14, (b.stacks (SubexpMainScalarAlphabet.stackMap alloc i)).length) ≤ _
  calc
    _ ≤ ∑ _i : Fin 14, W := Finset.sum_le_sum (fun i _ =>
      coefficient_frame_le alloc h hc _ (scalar_relevant alloc i)
        (scalar_ne_outputs alloc i).1 (scalar_ne_outputs alloc i).2)
    _ = 14 * W := by simp

theorem scalar_budget_le {er es W p r Q R : ℕ} [Fact p.Prime]
    (alloc : Allocation es) {a b : MainState er es} (h : RelevantWordBound W a)
    (hc : SubexpMainCoefficients.Result alloc a b p r Q R) :
    SubexpMainScalarAlphabet.runtimeBound alloc b p ≤ scalarBound W p := by
  have hs := scalar_selectedSize_le alloc h hc
  unfold SubexpMainScalarAlphabet.runtimeBound scalarBound
  gcongr

private theorem scalar_frame_at {er es : ℕ} (alloc : Allocation es)
    (a : MainState er es) (p : ℕ) [Fact p.Prime] (i : Fin 672)
    (hi : i.val < 661 ∨ 667 < i.val) (hs : 6 ≤ i.val) :
    (SubexpMainScalarAlphabet.installed alloc a p).stacks (ordinary alloc i) =
      a.stacks (ordinary alloc i) := by
  apply SubexpMainScalarAlphabet.installed_frame
  · intro j he
    have hv := congrArg (fun k : Fin (totalStacks es) => k.val) he
    change 640 + (21 + j.val) = i.val at hv
    omega
  · intro j he
    have hv := congrArg (fun k : Fin (totalStacks es) => k.val) he
    change j.val = i.val at hv
    omega

theorem frameWidth_budget_le {er es W p r Q R : ℕ} [Fact p.Prime]
    (alloc : Allocation es) {a b : MainState er es} (h : RelevantWordBound W a)
    (hc : SubexpMainCoefficients.Result alloc a b p r Q R) :
    SubexpMainScalarFrameWidth.runtimeBound alloc
      (SubexpMainScalarAlphabet.installed alloc b p) ≤ frameWidthBound W p := by
  have hsource :
      ((SubexpMainScalarAlphabet.installed alloc b p).stacks
        (SubexpMainScalarFrameWidth.sourcePort alloc)).length =
          2 * MatrixWordEncoding.width p + 1 := by
    have he := SubexpMainScalarAlphabet.installed_target alloc b p (5 : Fin 7)
    change (SubexpMainScalarAlphabet.installed alloc b p).stacks
      (SubexpMainScalarFrameWidth.sourcePort alloc) =
        Encoding.frame (MatrixWordEncoding.word p 0) at he
    rw [he, Encoding.length_frame, MatrixWordEncoding.word_length]
  have hwidth :
      ((SubexpMainScalarAlphabet.installed alloc b p).stacks
        (SubexpMainScalarFrameWidth.widthPort alloc)).length ≤ W := by
    rw [show SubexpMainScalarFrameWidth.widthPort alloc = ordinary alloc 660 from rfl,
      scalar_frame_at alloc b p 660 (Or.inl (by decide)) (by decide)]
    exact coefficient_frame_le alloc h hc _ (Or.inl (by change 660 < 672; decide))
      (by intro he; have hv := congrArg Fin.val he; change 660 = 649 at hv; omega)
      (by intro he; have hv := congrArg Fin.val he; change 660 = 254 at hv; omega)
  have hwork :
      ((SubexpMainScalarAlphabet.installed alloc b p).stacks
        (SubexpMainScalarFrameWidth.workPort alloc)).length ≤ W := by
    rw [show SubexpMainScalarFrameWidth.workPort alloc = ordinary alloc 319 from rfl,
      scalar_frame_at alloc b p 319 (Or.inl (by decide)) (by decide)]
    exact coefficient_frame_le alloc h hc _ (Or.inl (by change 319 < 672; decide))
      (by intro he; have hv := congrArg Fin.val he; change 319 = 649 at hv; omega)
      (by intro he; have hv := congrArg Fin.val he; change 319 = 254 at hv; omega)
  unfold SubexpMainScalarFrameWidth.runtimeBound frameWidthBound
  rw [hsource]
  omega

/-- The three actual stage budgets, evaluated at their actual intermediate
states, are bounded using only the incoming selected-word bound. -/
theorem three_stage_budget_le {er es W p r Q R : ℕ} [Fact p.Prime]
    (alloc : Allocation es) {a b : MainState er es} (h : RelevantWordBound W a)
    (hc : SubexpMainCoefficients.Result alloc a b p r Q R) :
    SubexpCoefficientProgram.budget p r Q R (SubexpMainLayoutChoices.selectedSize alloc a) +
      SubexpMainScalarAlphabet.runtimeBound alloc b p +
      SubexpMainScalarFrameWidth.runtimeBound alloc
        (SubexpMainScalarAlphabet.installed alloc b p) ≤ bound W p Q R := by
  exact Nat.add_le_add (Nat.add_le_add (coefficient_budget_le alloc h)
    (scalar_budget_le alloc h hc)) (frameWidth_budget_le alloc h hc)

/-- A single polynomial envelope retaining the real enumeration factor. -/
theorem bound_le_polynomial_times_power (W p Q R : ℕ) [Fact p.Prime] :
    bound W p Q R ≤
      22000001000 * (64 * W + p + Q + R + MatrixWordEncoding.width p + 2)^7 * p^R := by
  generalize hH : 64 * W + p + Q + R + MatrixWordEncoding.width p + 2 = H
  have h1 : 1 ≤ H := by omega
  have hs : 14 * W + p + 1 ≤ H := by omega
  have hw : MatrixWordEncoding.width p + 1 ≤ H := by omega
  have hp : 1 ≤ p^R := Nat.one_le_pow _ _ (Fact.out : p.Prime).one_lt.le
  have hscalar : scalarBound W p ≤ 500 * H^7 * p^R := by
    calc
      scalarBound W p ≤ 500 * H * H := by unfold scalarBound; gcongr
      _ = 500 * H^2 := by ring
      _ ≤ 500 * H^7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right h1 (by decide : 2 ≤ 7))
      _ ≤ 500 * H^7 * p^R := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (500 * H^7) hp
  have hwidth : frameWidthBound W p ≤ 23 * H^7 * p^R := by
    have hlinear : frameWidthBound W p ≤ 23 * H := by unfold frameWidthBound; omega
    calc
      frameWidthBound W p ≤ 23 * H := hlinear
      _ ≤ 23 * H^7 := Nat.mul_le_mul_left _ (by
        simpa only [pow_one] using Nat.pow_le_pow_right h1 (by decide : 1 ≤ 7))
      _ ≤ 23 * H^7 * p^R := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (23 * H^7) hp
  unfold bound coefficientBound
  rw [hH]
  calc
    _ ≤ 22000000000 * H^7 * p^R + 500 * H^7 * p^R + 23 * H^7 * p^R :=
      Nat.add_le_add (Nat.add_le_add_left hscalar _) hwidth
    _ = 22000000523 * H^7 * p^R := by ring
    _ ≤ 22000001000 * H^7 * p^R := by gcongr; decide

end SubexponentialSAT.SubexpMainLayoutCoefficientBounds

end OAI.Algorithms
