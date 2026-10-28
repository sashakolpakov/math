import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingTupleBounds
import OAI.Algorithms.SubexponentialSAT.SubexpTupleRefinement

namespace OAI.Algorithms

/-! Runtime Boolean head enumeration by the audited fixed-control tuple
program. Only the supplied head dimension is exponentiated. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.TupleProgram SubexponentialSAT.SubexpTupleRefinement

def boolCode : SubexponentialSAT.StackEncoding.BlockCode Bool where
  width := 1
  width_pos := by decide
  block b := [b]
  length_block _ := rfl
  injective_block := by intro a b h; simpa using h

def alphabet : List (List Bool) := [[false], [true]]
def assignments (h : ℕ) : List (List Bool) := powerRows alphabet h [[]]

@[simp] theorem alphabet_length : alphabet.length = 2 := rfl

@[simp] theorem assignments_length (h : ℕ) : (assignments h).length = 2^h := by
  simp [assignments, generated_count]

theorem encode_bool_eq {h : ℕ} (x : Fin h → Bool) :
    encodeTuple boolCode x = List.ofFn x := by
  simp [encodeTuple, SubexponentialSAT.StackEncoding.encodeDataStack_eq_flatMap, boolCode]

theorem assignments_complete {h : ℕ} (x : Fin h → Bool) :
    List.ofFn x ∈ assignments h := by
  have hx := encodeTuple_mem_powerRows boolCode [false, true]
    (by intro b; cases b <;> simp) h x
  rw [encode_bool_eq] at hx
  simpa [boolCode, assignments, alphabet] using hx

theorem assignments_sound {h : ℕ} {bits : List Bool}
    (hbits : bits ∈ assignments h) : ∃ x : Fin h → Bool, List.ofFn x = bits := by
  have hm : bits ∈ powerRows ([false, true].map boolCode.block) h [[]] := by
    simpa [assignments, alphabet, boolCode] using hbits
  obtain ⟨x, _, hx⟩ := (mem_powerRows_encoded boolCode [false, true] h bits).mp hm
  exact ⟨x, (encode_bool_eq x).symm.trans hx⟩

theorem assignments_nodup (h : ℕ) : (assignments h).Nodup := by
  have hx := powerRows_encoded_nodup boolCode [false, true] (by decide) h
  simpa [assignments, alphabet, boolCode] using hx

theorem assignment_width {h : ℕ} {bits : List Bool}
    (hbits : bits ∈ assignments h) : bits.length = h := by
  obtain ⟨x, rfl⟩ := assignments_sound hbits
  exact List.length_ofFn

def enumerationCost (h : ℕ) : ℕ :=
  800 * (h+1) * (2^h+1) * (h+2) + 9

abbrev enumerationProgram := generateProgram

theorem enumeration_control_size : size generateCmd + 1 = 83 := generate_control_size

def enumerationInput (h : ℕ) : State 10 9 :=
  ⟨fun _ => false, fun i =>
    if i = 1 then ProgramEncoding.encodeRecords alphabet
    else if i = 8 then List.replicate h false else []⟩

theorem enumeration_runsIn (h : ℕ) :
    ∃ next : State 10 9,
      next.stacks 0 = ProgramEncoding.encodeRecords (assignments h) ∧
      next.stacks 8 = [] ∧
      RunsIn enumerationProgram (enumerationCost h)
        ((enumerationInput h).withPC (some enumerationProgram.entry))
        (next.withPC none) := by
  have hi : outerInvariant alphabet (List.replicate h false) false
      (enumerationInput h) := by simp [outerInvariant, enumerationInput]
  obtain ⟨next, hnext, k, hk, he⟩ := generateProgram_runsIn alphabet
    (List.replicate h false) false (enumerationInput h) hi
    (by simp [enumerationInput]) (by simp [enumerationInput])
    (by simp [enumerationInput])
  refine ⟨next, ?_, hnext.1.2.2.2.2.2.1, k, ?_, he⟩
  · simpa [assignments] using hnext.2.1
  · have hb := SubexponentialSAT.Subexp.PackingTupleBounds.generated_powerCost_le alphabet h 1
      (by intro word hw; simp [alphabet] at hw; rcases hw with rfl | rfl <;> simp)
    apply hk.trans
    simpa [enumerationCost, alphabet] using Nat.add_le_add_right hb 9

theorem enumeration_primitive (h : ℕ) :
    ∃ next : State 10 9,
      next.stacks 0 = ProgramEncoding.encodeRecords (assignments h) ∧
      next.stacks 8 = [] ∧
      Computation.RunsIn (primitive enumerationProgram).step
        (primitiveOverhead enumerationProgram * enumerationCost h)
        (primitiveCfg enumerationProgram
          ((enumerationInput h).withPC (some enumerationProgram.entry)))
        (primitiveCfg enumerationProgram (next.withPC none)) := by
  obtain ⟨next, hout, hdepth, hrun⟩ := enumeration_runsIn h
  exact ⟨next, hout, hdepth, primitive_execution enumerationProgram hrun⟩

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
