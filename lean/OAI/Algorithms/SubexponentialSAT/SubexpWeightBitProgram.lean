import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpWeightControl
import OAI.Algorithms.SubexponentialSAT.SubexpNegationProgram

namespace OAI.Algorithms

/-!
# Concrete serialized monomial-weight machine

This module discharges the scalar-service contract using the actual verified
149-label modular multiplication program. The resulting 219-label program is
independent of the dimension, modulus, exponent, and input record list.
-/

namespace SubexponentialSAT.SubexpWeightBitProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic
open scoped BigOperators

private theorem scalarStacks_eq (acc modulus base : List Bool) :
    SubexpWeightControl.scalarStacks acc modulus base =
      SubexpNegationProgram.state acc modulus base := by
  funext i
  fin_cases i <;> rfl

instance concreteScalarService : SubexpWeightControl.ScalarService where
  program := SubexpNegationProgram.negationProgram
  execute := by
    intro regs input modulus constant B hx hc hmLength hm hcapacity
    have hentry : SubexpNegationProgram.negationProgram.entry = (0 : Fin 149) := by
      apply Fin.ext
      rfl
    rw [hentry]
    simpa only [scalarStacks_eq] using
      SubexpNegationProgram.negation_execute regs input modulus constant B hx hc hmLength hm hcapacity

export SubexpWeightControl (Data Shape weightStacks stacks_shape shape_stacks shape_of_stacks
  WeightRecord payload encodeRecords recordValue recordsValue powerSteps recordSteps
  recordsFlag afterTag encodeRecords_tag scanSteps exponentTotal recordSteps_le
  scanSteps_le retained_scanSteps_le recordsFor recordsValue_recordsFor
  recordsValue_coordinateWeight recordsValue_momentWeight retained_recordsFor_bound)

abbrev powerCommand := SubexpWeightControl.powerCommand
abbrev powerProgram := SubexpWeightControl.powerProgram
abbrev processRecord := SubexpWeightControl.processRecord
abbrev recordsLoop := SubexpWeightControl.recordsLoop
abbrev weightCommand := SubexpWeightControl.weightCommand
abbrev weightProgram := SubexpWeightControl.weightProgram

theorem powerProgram_labels : size powerCommand + 1 = 184 :=
  SubexpWeightControl.powerProgram_labels

theorem weightProgram_labels : size weightCommand + 1 = 219 :=
  SubexpWeightControl.weightProgram_labels

theorem power_execute (d : Data) (initial modulus base source : List Bool) (B : ℕ)
    (hd : Shape d initial modulus base source) (hs : d.stacks 10 = [])
    (ha : initial.length = B) (hb : base.length = B)
    (hmLength : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ (e : Data) (output : List Bool),
      RunsIn powerProgram
        (BinaryArithmetic.toNat (d.stacks 9) * (6010 * (B + 1) ^ 2) +
          (BinaryArithmetic.toNat (d.stacks 9) + 1) * (16 * (d.stacks 9).length + 16) + 1)
        (d.withPC (some powerProgram.entry)) (e.withPC none) ∧
      Shape e output modulus base source ∧ output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) *
          (BinaryArithmetic.toNat base : ZMod (BinaryArithmetic.toNat modulus)) ^ BinaryArithmetic.toNat (d.stacks 9) ∧
      BinaryArithmetic.toNat (e.stacks 9) = 0 ∧ (e.stacks 9).length = (d.stacks 9).length ∧
      e.stacks 10 = [] := by
  exact SubexpWeightControl.power_execute d initial modulus base source B hd hs ha hb hmLength hm hcapacity

theorem processRecord_execute (d : Data) (initial modulus tail : List Bool)
    (r : WeightRecord) (B : ℕ)
    (hd : d.stacks = weightStacks initial modulus [] [] (payload r ++ tail))
    (ha : initial.length = B) (hb : r.base.length = B)
    (hmLength : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ (n : ℕ) (e : Data) (output : List Bool), n ≤ recordSteps B r ∧ Eval processRecord n d e ∧
      e.stacks = weightStacks output modulus [] [] tail ∧ output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) * recordValue (BinaryArithmetic.toNat modulus) r := by
  exact SubexpWeightControl.processRecord_execute d initial modulus tail r B hd ha hb hmLength hm hcapacity

theorem recordsLoop_execute (rs : List WeightRecord) (d : Data)
    (initial modulus suffix : List Bool) (B : ℕ)
    (hd : d.stacks = weightStacks initial modulus [] [] (afterTag rs suffix))
    (hf : d.regs 7 = recordsFlag rs) (ha : initial.length = B)
    (hb : ∀ r ∈ rs, r.base.length = B)
    (hmLength : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ (n : ℕ) (e : Data) (output : List Bool), n ≤ scanSteps B rs ∧ Eval recordsLoop n d e ∧
      e.stacks = weightStacks output modulus [] [] suffix ∧ output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) * recordsValue (BinaryArithmetic.toNat modulus) rs := by
  exact SubexpWeightControl.recordsLoop_execute rs d initial modulus suffix B hd hf ha hb hmLength hm hcapacity

theorem weight_execute (rs : List WeightRecord) (d : Data)
    (initial modulus suffix : List Bool) (B : ℕ)
    (hd : d.stacks = weightStacks initial modulus [] [] (encodeRecords rs ++ suffix))
    (ha : initial.length = B) (hb : ∀ r ∈ rs, r.base.length = B)
    (hmLength : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ (e : Data) (output : List Bool), RunsIn weightProgram (scanSteps B rs + 2)
        (d.withPC (some weightProgram.entry)) (e.withPC none) ∧
      e.stacks = weightStacks output modulus [] [] suffix ∧ output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) * recordsValue (BinaryArithmetic.toNat modulus) rs := by
  exact SubexpWeightControl.weight_execute rs d initial modulus suffix B hd ha hb hmLength hm hcapacity

theorem weight_primitive (rs : List WeightRecord) (d : Data)
    (initial modulus suffix : List Bool) (B : ℕ)
    (hd : d.stacks = weightStacks initial modulus [] [] (encodeRecords rs ++ suffix))
    (ha : initial.length = B) (hb : ∀ r ∈ rs, r.base.length = B)
    (hmLength : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ (e : Data) (output : List Bool), Computation.RunsIn (primitive weightProgram).step
        (primitiveOverhead weightProgram * (scanSteps B rs + 2))
        (primitiveCfg weightProgram (d.withPC (some weightProgram.entry)))
        (primitiveCfg weightProgram (e.withPC none)) ∧
      e.stacks = weightStacks output modulus [] [] suffix ∧ output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) * recordsValue (BinaryArithmetic.toNat modulus) rs := by
  exact SubexpWeightControl.weight_primitive rs d initial modulus suffix B hd ha hb hmLength hm hcapacity

theorem weight_execute_moment {D : ℕ} (support : List (Fin D)) (hn : support.Nodup)
    (indices coordinates exponents : Fin D → List Bool)
    (a : Fin D →₀ ℕ) (hexp : ∀ i, BinaryArithmetic.toNat (exponents i) = a i)
    (hcover : ∀ i ∈ a.support, i ∈ support)
    (d : Data) (initial modulus suffix : List Bool) (B : ℕ)
    (hd : d.stacks = weightStacks initial modulus [] []
      (encodeRecords (recordsFor support indices coordinates exponents) ++ suffix))
    (ha : initial.length = B) (hunit : (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) = 1)
    (hb : ∀ i ∈ support, (coordinates i).length = B)
    (hmLength : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ (e : Data) (output : List Bool), RunsIn weightProgram
        (scanSteps B (recordsFor support indices coordinates exponents) + 2)
        (d.withPC (some weightProgram.entry)) (e.withPC none) ∧
      e.stacks = weightStacks output modulus [] [] suffix ∧ output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        Moments.weight a (fun i => (BinaryArithmetic.toNat (coordinates i) : ZMod (BinaryArithmetic.toNat modulus))) := by
  exact SubexpWeightControl.weight_execute_moment support hn indices coordinates exponents a hexp hcover d initial modulus suffix B hd ha hunit hb hmLength hm hcapacity

/-- A partial support computes exactly the corresponding coordinate weight;
the exponent may be nonzero outside the supplied support. -/
theorem weight_execute_coordinateWeight {D : ℕ} (support : List (Fin D)) (hn : support.Nodup)
    (indices coordinates exponents : Fin D → List Bool)
    (a : Fin D → ℕ) (hexp : ∀ i, BinaryArithmetic.toNat (exponents i) = a i)
    (d : Data) (initial modulus suffix : List Bool) (B : ℕ)
    (hd : d.stacks = weightStacks initial modulus [] []
      (encodeRecords (recordsFor support indices coordinates exponents) ++ suffix))
    (ha : initial.length = B) (hunit : (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) = 1)
    (hb : ∀ i ∈ support, (coordinates i).length = B)
    (hmLength : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ (e : Data) (output : List Bool), RunsIn weightProgram
        (scanSteps B (recordsFor support indices coordinates exponents) + 2)
        (d.withPC (some weightProgram.entry)) (e.withPC none) ∧
      e.stacks = weightStacks output modulus [] [] suffix ∧ output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        Separation.coordinateWeight support.toFinset id a
          (fun i => (BinaryArithmetic.toNat (coordinates i) : ZMod (BinaryArithmetic.toNat modulus))) := by
  obtain ⟨e, output, ht, hs, ho, hv⟩ := weight_execute
    (recordsFor support indices coordinates exponents) d initial modulus suffix B hd ha
    (by
      intro r hr
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
      exact hb i hi) hmLength hm hcapacity
  refine ⟨e, output, ht, hs, ho, ?_⟩
  rw [hv, hunit, one_mul, recordsValue_coordinateWeight _ _ hn]
  simp only [hexp]

/-- Actual primitive-machine execution for a retained monomial. All growing
parameters remain explicit; the only outer multiplier is the compiler overhead
of this fixed 219-label instruction table. -/
theorem weight_retained_primitive {D : ℕ} (support : List (Fin D)) (hn : support.Nodup)
    (indices coordinates exponents : Fin D → List Bool)
    (a : Fin D →₀ ℕ) (hexp : ∀ i, BinaryArithmetic.toNat (exponents i) = a i)
    (hcover : ∀ i ∈ a.support, i ∈ support)
    (hdegree : (∑ i, a i) ≤ 2 * D + 1)
    (d : Data) (initial modulus suffix : List Bool) (B I E : ℕ)
    (hd : d.stacks = weightStacks initial modulus [] []
      (encodeRecords (recordsFor support indices coordinates exponents) ++ suffix))
    (ha : initial.length = B) (hunit : (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) = 1)
    (hb : ∀ i ∈ support, (coordinates i).length = B)
    (hi : ∀ i ∈ support, (indices i).length ≤ I)
    (he : ∀ i ∈ support, (exponents i).length ≤ E)
    (hmLength : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ (e : Data) (output : List Bool), Computation.RunsIn (primitive weightProgram).step
        (primitiveOverhead weightProgram *
          ((2 * D + 1) * (6010 * (B + 1) ^ 2 + 16 * E + 16) +
            D * (5 * I + 8 * B + 24 * E + 37) + 3))
        (primitiveCfg weightProgram (d.withPC (some weightProgram.entry)))
        (primitiveCfg weightProgram (e.withPC none)) ∧
      e.stacks = weightStacks output modulus [] [] suffix ∧ output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        Moments.weight a (fun i => (BinaryArithmetic.toNat (coordinates i) : ZMod (BinaryArithmetic.toNat modulus))) := by
  obtain ⟨e, output, ht, hs, ho, hv⟩ := weight_execute_moment support hn indices coordinates
    exponents a hexp hcover d initial modulus suffix B hd ha hunit hb hmLength hm hcapacity
  have hbound := retained_recordsFor_bound B I E support hn indices coordinates exponents
    (by simpa only [hexp] using hdegree) hi he
  exact ⟨e, output, BitProgram.primitive_execution _ (ht.mono hbound), hs, ho, hv⟩

/-- The outside and individual color factors use the same concrete machine
and retained-degree time bound, without a full-support assumption. -/
theorem weight_retained_coordinate_primitive {D : ℕ}
    (support : List (Fin D)) (hn : support.Nodup)
    (indices coordinates exponents : Fin D → List Bool)
    (a : Fin D → ℕ) (hexp : ∀ i, BinaryArithmetic.toNat (exponents i) = a i)
    (hdegree : (∑ i, a i) ≤ 2 * D + 1)
    (d : Data) (initial modulus suffix : List Bool) (B I E : ℕ)
    (hd : d.stacks = weightStacks initial modulus [] []
      (encodeRecords (recordsFor support indices coordinates exponents) ++ suffix))
    (ha : initial.length = B) (hunit : (BinaryArithmetic.toNat initial : ZMod (BinaryArithmetic.toNat modulus)) = 1)
    (hb : ∀ i ∈ support, (coordinates i).length = B)
    (hi : ∀ i ∈ support, (indices i).length ≤ I)
    (he : ∀ i ∈ support, (exponents i).length ≤ E)
    (hmLength : modulus.length ≤ B + 1) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ B) :
    ∃ (e : Data) (output : List Bool), Computation.RunsIn (primitive weightProgram).step
        (primitiveOverhead weightProgram *
          ((2 * D + 1) * (6010 * (B + 1) ^ 2 + 16 * E + 16) +
            D * (5 * I + 8 * B + 24 * E + 37) + 3))
        (primitiveCfg weightProgram (d.withPC (some weightProgram.entry)))
        (primitiveCfg weightProgram (e.withPC none)) ∧
      e.stacks = weightStacks output modulus [] [] suffix ∧ output.length = B ∧
      (BinaryArithmetic.toNat output : ZMod (BinaryArithmetic.toNat modulus)) =
        Separation.coordinateWeight support.toFinset id a
          (fun i => (BinaryArithmetic.toNat (coordinates i) : ZMod (BinaryArithmetic.toNat modulus))) := by
  obtain ⟨e, output, ht, hs, ho, hv⟩ := weight_execute_coordinateWeight support hn indices
    coordinates exponents a hexp d initial modulus suffix B hd ha hunit hb hmLength hm hcapacity
  have hbound := retained_recordsFor_bound B I E support hn indices coordinates exponents
    (by simpa only [hexp] using hdegree) hi he
  exact ⟨e, output, BitProgram.primitive_execution _ (ht.mono hbound), hs, ho, hv⟩

end SubexponentialSAT.SubexpWeightBitProgram

end OAI.Algorithms
