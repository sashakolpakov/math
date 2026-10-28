import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedTupleProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation

namespace OAI.Algorithms

/-!
# Ordered pair and quartic calls in the coefficient-search workspace

These are actual relocated calls of the fixed-depth tuple program. The
coefficient-search controller uses the two fixed instances at depths 2 and 4.
All storage outside the listed workspace, including the cached modulus and
the other candidate table, is preserved.
-/

namespace SubexponentialSAT.SubexpQuarticTupleCalls

open BitProgram StructuredCalls Subexp.TupleProgram SubexpOrderedTupleData
open Subexp.BlockSearchPreparation (restrictState lifted_call)

abbrev Data := State 14 35

def registers (i : Fin 10) : Fin 14 := Fin.castAdd 4 i
def stackMap (output : Fin 35) : Fin 9 → Fin 35 :=
  ![output, 25, 0, 1, 2, 3, 4, 5, 6]

theorem registers_injective : Function.Injective registers := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 14 => k.val) h)

theorem stackMap_injective (output : Fin 35) (ho : output = 26 ∨ output = 28) :
    Function.Injective (stackMap output) := by
  rcases ho with rfl | rfl <;> decide

abbrev call (n : ℕ) (output : Fin 35) : Cmd 14 35 :=
  .call (ProgramLinking.liftProgram (SubexpOrderedTupleProgram.program n)
    registers (stackMap output))

def clean (a : Data) : Prop :=
  a.stacks 0 = [] ∧ a.stacks 1 = [] ∧ a.stacks 2 = [] ∧
    a.stacks 4 = [] ∧ a.stacks 5 = []

structure Input (destination : Fin 35) (alphabetWords : List (List Bool)) (a : Data) : Prop where
  output_empty : a.stacks destination = []
  alphabet : a.stacks 25 = ProgramEncoding.encodeRecords alphabetWords
  clean : clean a
  marker_empty : a.stacks 3 = []

structure Completed (n : ℕ) (destination : Fin 35) (alphabetWords : List (List Bool))
    (before after : Data) : Prop where
  output : after.stacks destination =
    ProgramEncoding.encodeRecords (orderedRows alphabetWords n [[]])
  alphabet : after.stacks 25 = ProgramEncoding.encodeRecords alphabetWords
  clean : clean after
  marker : after.stacks 3 = [false]
  depth : after.stacks 6 = before.stacks 6
  guard : after.regs 9 = before.regs 9
  stack_frame : ∀ i : Fin 35, 7 ≤ i.val → i ≠ 25 → i ≠ destination →
    after.stacks i = before.stacks i
  register_frame : ∀ i : Fin 14, 10 ≤ i.val → after.regs i = before.regs i

/-- The only table destinations used by the search are 26 (pairs) and 28
(quartics). The complete other table is therefore preserved by each call. -/
theorem call_eval (n : ℕ) (output : Fin 35) (ho : output = 26 ∨ output = 28)
    (alphabet : List (List Bool)) (a : Data) (ha : Input output alphabet a) :
    ∃ k next, k ≤ SubexpOrderedTupleProgram.cost alphabet n ∧
      Completed n output alphabet a next ∧ Eval (call n output) k a next := by
  let small := restrictState registers (stackMap output) a
  have hσ := stackMap_injective output ho
  have hi : outerInvariant alphabet (a.stacks 6) (a.regs 9) small := by
    rcases ha.clean with ⟨h0, h1, h2, h4, h5⟩
    simpa [outerInvariant, small, restrictState, registers, stackMap] using
      (show a.stacks 25 = ProgramEncoding.encodeRecords alphabet ∧
        a.stacks 1 = [] ∧ a.stacks 2 = [] ∧ a.stacks 4 = [] ∧ a.stacks 5 = [] ∧
        a.stacks 6 = a.stacks 6 ∧ a.regs 9 = a.regs 9 from
        ⟨ha.alphabet, h1, h2, h4, h5, rfl, rfl⟩)
  have h0 : small.stacks 0 = [] := ha.output_empty
  have h2 : small.stacks 2 = [] := ha.clean.1
  have h5 : small.stacks 5 = [] := ha.marker_empty
  obtain ⟨b, hb, hr⟩ := SubexpOrderedTupleProgram.program_runsIn n alphabet
    (a.stacks 6) (a.regs 9) small hi h0 h2 h5
  obtain ⟨k, hk, he⟩ := lifted_call (SubexpOrderedTupleProgram.program n)
    registers (stackMap output) registers_injective hσ a b
    (SubexpOrderedTupleProgram.cost alphabet n) hr
  let next := embedState registers (stackMap output) a b
  have hs (i : Fin 9) : next.stacks (stackMap output i) = b.stacks i :=
    embedState_stack registers (stackMap output) a b hσ i
  have hreg (i : Fin 10) : next.regs (registers i) = b.regs i :=
    embedState_register registers (stackMap output) a b registers_injective i
  rcases hb with ⟨⟨hb1, hb3, hb4, hb6, hb7, hb8, hb9⟩, hb0, hb2, hb5⟩
  refine ⟨k, next, hk, ?_, he⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hs 0).trans hb0
  · exact (hs 1).trans hb1
  · exact ⟨(hs 2).trans hb2, (hs 3).trans hb3, (hs 4).trans hb4,
      (hs 6).trans hb6, (hs 7).trans hb7⟩
  · exact (hs 5).trans hb5
  · exact (hs 8).trans hb8
  · exact (hreg 9).trans hb9
  · intro i hi hi25 hio
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    fin_cases j <;> simp [stackMap] at hj
    all_goals first
      | exact hio hj.symm
      | exact hi25 hj.symm
      | have hv := congrArg (fun z : Fin 35 => z.val) hj
        norm_num at hv
        omega
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hv := congrArg (fun z : Fin 14 => z.val) hj
    change j.val = i.val at hv
    omega

theorem Completed.pair_table_preserved {alphabet : List (List Bool)} {a b : Data}
    (h : Completed 4 28 alphabet a b) : b.stacks 26 = a.stacks 26 :=
  h.stack_frame 26 (by decide) (by decide) (by decide)

theorem Completed.cached_modulus_preserved {n output alphabet} {a b : Data}
    (h : Completed n output alphabet a b) (ho : output = 26 ∨ output = 28) :
    b.stacks 19 = a.stacks 19 ∧ b.stacks 31 = a.stacks 31 := by
  have h19 : (19 : Fin 35) ≠ output := by rcases ho with rfl | rfl <;> decide
  have h31 : (31 : Fin 35) ≠ output := by rcases ho with rfl | rfl <;> decide
  exact ⟨h.stack_frame 19 (by decide) (by decide) h19,
    h.stack_frame 31 (by decide) (by decide) h31⟩

theorem Completed.selected_output {n p : ℕ} [Fact p.Prime] {output : Fin 35}
    {a b : Data}
    (h : Completed n output
      ((QuarticSearch.elements p).map (SubexpEnumerationPayload.scalarCode p).block) a b) :
    b.stacks output = ProgramEncoding.encodeRecords
      ((QuarticSearch.vectors (QuarticSearch.elements p) n).map
        (SubexpTupleRefinement.encodeTuple (SubexpEnumerationPayload.scalarCode p))) := by
  simpa only [orderedRows_encoded] using h.output

end SubexponentialSAT.SubexpQuarticTupleCalls

end OAI.Algorithms
