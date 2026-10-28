import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecCleanLiteralsProgram
import OAI.Algorithms.SubexponentialSAT.SubexpTautologyFilterProgram

namespace OAI.Algorithms

/-!+# Actual literal cleanup followed by tautology removal

This is a fixed program on the original declared variable universe. Its two
stages use the same input/output port and restore empty work stacks. The exact
list order and the length bound are retained for subsequent clause absorption.
-/

namespace SubexponentialSAT.SubexpNormalizationPrefixProgram

open BitProgram StructuredCalls

abbrev Data := State 13 11
abbrev Ready := ExecCleanLiteralsProgram.Ready
abbrev formulaCode := ExecCleanLiteralsProgram.formulaCode

def preprocess (F : List (List ℕ)) : List (List ℕ) :=
  ExecCNF.removeTautologies SubexpFrontend.negateCode (ExecCNF.cleanLiterals F)

abbrev command : Cmd 13 11 :=
  .seq ExecCleanLiteralsProgram.clean SubexpTautologyFilterProgram.filter

theorem preprocess_length_le (F : List (List ℕ)) :
    (formulaCode (preprocess F)).length ≤ (formulaCode F).length :=
  (SubexpTautologyFilterProgram.filtered_length_le (ExecCNF.cleanLiterals F)).trans
    (ExecCleanLiteralsProgram.cleaned_length_le F)

theorem command_eval (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = formulaCode F) (hready : Ready d) :
    ∃ n ≤ 999 * ((formulaCode F).length + 1) ^ 2, ∃ e : Data,
      Eval command n d e ∧ Ready e ∧ e.stacks 0 = formulaCode (preprocess F) := by
  obtain ⟨n, hn, middle, hclean, hmiddle, hout⟩ :=
    ExecCleanLiteralsProgram.clean_eval F d hsource hready
  have hnext : SubexpTautologyFilterProgram.Ready middle :=
    (SubexpTautologyFilterProgram.ready_iff middle).mpr
      ((ExecCleanLiteralsProgram.ready_iff middle).mp hmiddle)
  obtain ⟨m, hm, e, hfilter, he, heout⟩ :=
    SubexpTautologyFilterProgram.filter_eval (ExecCNF.cleanLiterals F) middle hout hnext
  have hlen := ExecCleanLiteralsProgram.cleaned_length_le F
  have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hlen 1) 2
  have hm' : m ≤ 399 * ((formulaCode F).length + 1) ^ 2 :=
    hm.trans (Nat.mul_le_mul_left 399 hsq)
  refine ⟨n + m, ?_, e, hclean.seq hfilter, ?_, heout⟩
  · nlinarith
  · exact (ExecCleanLiteralsProgram.ready_iff e).mpr
      ((SubexpTautologyFilterProgram.ready_iff e).mp he)

def program := compiled command 0 0

theorem program_runsIn (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = formulaCode F) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 0 = formulaCode (preprocess F) ∧
      RunsIn program (1000 * ((formulaCode F).length + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨n, hn, e, he, hready', hout⟩ := command_eval F d hsource hready
  refine ⟨e, hready', hout, n + 1, ?_, compiled_halt_trace he 0 0⟩
  have hpos : 0 < ((formulaCode F).length + 1) ^ 2 := pow_pos (by omega) _
  omega

theorem raw_input_runsIn (F : List (List ℕ)) :
    ∃ e : Data, Ready e ∧ e.stacks 0 = formulaCode (preprocess F) ∧
      RunsIn program (1000 * ((formulaCode F).length + 1) ^ 2)
        (initial program (formulaCode F)) (e.withPC none) := by
  let d := SubexpTautologyFilterProgram.inputData (formulaCode F)
  have hd : Ready d := (ExecCleanLiteralsProgram.ready_iff d).mpr
    ((SubexpTautologyFilterProgram.ready_iff d).mp
      (SubexpTautologyFilterProgram.inputData_ready _))
  have hsource : d.stacks 0 = formulaCode F := by
    simp [d, SubexpTautologyFilterProgram.inputData]
  obtain ⟨e, he, hout, hrun⟩ := program_runsIn F d hsource hd
  exact ⟨e, he, hout, hrun⟩

theorem primitive_execution (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 0 = formulaCode F) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 0 = formulaCode (preprocess F) ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (1000 * ((formulaCode F).length + 1) ^ 2))
        (primitiveCfg program (d.withPC (some program.entry)))
        (primitiveCfg program (e.withPC none)) := by
  obtain ⟨e, he, hout, hrun⟩ := program_runsIn F d hsource hready
  exact ⟨e, he, hout, BitProgram.primitive_execution program hrun⟩

theorem raw_input_primitive (F : List (List ℕ)) :
    ∃ e : Data, Ready e ∧ e.stacks 0 = formulaCode (preprocess F) ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (1000 * ((formulaCode F).length + 1) ^ 2))
        ((primitive program).init (formulaCode F))
        (primitiveCfg program (e.withPC none)) := by
  obtain ⟨e, he, hout, hrun⟩ := raw_input_runsIn F
  exact ⟨e, he, hout, by
    simpa only [primitive_initial] using BitProgram.primitive_execution program hrun⟩

end SubexponentialSAT.SubexpNormalizationPrefixProgram

end OAI.Algorithms
