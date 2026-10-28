import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldNodes
import OAI.Algorithms.SubexponentialSAT.PositiveWordProgram

namespace OAI.Algorithms

/-!
# Exact bit predicate for filtering the explicit field-node table

The fixed seven-label positivity scanner tests the actual coefficient payload.
The interpretation theorem below needs no abstract field equality instruction.
Composition of the scanner with record copying and emission is a separate
machine-program layer.
-/

namespace SubexponentialSAT.SubexpNodeFilterSpec

open SubexpFieldNodes SubexpQuarticRing

variable (p : ℕ) [Fact p.Prime]

theorem coefficient_nonzero_iff (c : Coefficients p) :
    c ≠ 0 ↔ c 0 ≠ 0 ∨ c 1 ≠ 0 ∨ c 2 ≠ 0 ∨ c 3 ≠ 0 := by
  constructor
  · intro hc
    by_contra hn
    simp only [not_or, not_not] at hn
    apply hc
    funext i
    fin_cases i <;> simp_all
  · intro h hz
    subst c
    simp at h

theorem true_mem_liftedCoefficient (μ : ℕ) (hμ : 0 < μ)
    (c : Coefficients p) (i : Fin 4) :
    true ∈ SubexpLiftRing.encodeBase p μ (liftCoefficients p μ c i) ↔ c i ≠ 0 := by
  rw [← PositiveWordProgram.positive_eq_true_iff_mem,
    PositiveWordProgram.positive_iff, SubexpLiftRing.encodeBase_value,
    liftCoefficients_val p μ hμ]
  rw [Nat.pos_iff_ne_zero]
  exact (ZMod.val_eq_zero (c i)).not

/-- On the actual four-word payload the fixed scanner is exactly the
nonzero-vector predicate used by the executable node list. -/
theorem positive_liftQuad_iff (μ : ℕ) (hμ : 0 < μ) (c : Coefficients p) :
    PositiveWordProgram.positive
      (SubexpQuarticEncoding.encodeQuad p μ (liftQuad p μ c)) = true ↔ c ≠ 0 := by
  rw [PositiveWordProgram.positive_eq_true_iff_mem]
  simp only [SubexpQuarticEncoding.encodeQuad, liftQuad, Quad.ofFn,
    List.mem_append, true_mem_liftedCoefficient p μ hμ, or_assoc]
  exact (coefficient_nonzero_iff p c).symm

theorem positive_encodeCoefficients_iff (c : Coefficients p) :
    PositiveWordProgram.positive (encodeCoefficients p c) = true ↔ c ≠ 0 :=
  positive_liftQuad_iff p 1 (by decide) c

theorem positive_encodeCoefficients (c : Coefficients p) :
    PositiveWordProgram.positive (encodeCoefficients p c) = decide (c ≠ 0) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using positive_encodeCoefficients_iff p c

/-- The scanner may read the parser's reversed payload: OR does not depend
on bit order. -/
theorem positive_reverse (xs : List Bool) :
    PositiveWordProgram.positive xs.reverse = PositiveWordProgram.positive xs := by
  apply Bool.eq_iff_iff.mpr
  simp only [PositiveWordProgram.positive_eq_true_iff_mem, List.mem_reverse]

theorem filter_encodedCoefficients (cs : List (Coefficients p)) :
    (cs.map (encodeCoefficients p)).filter PositiveWordProgram.positive =
      (cs.filter (fun c => decide (c ≠ 0))).map (encodeCoefficients p) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro c _
  exact positive_encodeCoefficients p c

/-- Filtering the encoded all-vector list gives exactly the proved field
node table in its existing explicit order. -/
theorem filter_allData :
    ((allData p).map (encodeCoefficients p)).filter PositiveWordProgram.positive =
      encodedFieldData p :=
  filter_encodedCoefficients p (allData p)

/-- One genuine primitive execution of the fixed scanner on any coefficient
record, with the already proved compiler and linear scan bounds. -/
theorem primitive_outputs (c : Coefficients p) :
    (BitProgram.primitive PositiveWordProgram.program).OutputsInTime
      (encodeCoefficients p c) (decide (c ≠ 0))
      (BitProgram.primitiveOverhead PositiveWordProgram.program *
        (3 * (4 * (Nat.log 2 p + 1)) + 5)) := by
  simpa only [positive_encodeCoefficients p c, encodeCoefficients_length] using
    PositiveWordProgram.primitive_outputs (encodeCoefficients p c)

end SubexponentialSAT.SubexpNodeFilterSpec

end OAI.Algorithms
