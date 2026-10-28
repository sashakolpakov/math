import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowEmitCall

namespace OAI.Algorithms

/-! One fixed producer from packed scalar/cache tables to row postfix bytes. -/

namespace SubexponentialSAT.Subexp.UniversalRowSourceProgram

open BitProgram StructuredCalls
open UniversalRowGather (Data Word)
open UniversalRowLoop (Tables Valid ready)

abbrev command : Cmd 8 32 :=
  .seq UniversalRowDataProgram.command UniversalRowEmitCall.command

abbrev program : Program 8 32 (size command + 1) := compiled command 31 31

def bound (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    (delta limit zero one : Word) : ℕ :=
  UniversalRowDataProgram.cost t width rowWidth positions delta limit +
    2048 * UniversalRowProgram.inputSize zero one
      (UniversalRowDataProgram.row t positions delta limit) ^ 2 + 4

theorem program_runsIn (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    (valid : Valid t width rowWidth positions) (delta limit zero one : Word) (a : Data)
    (ha : ready t width rowWidth positions a)
    (hd : a.stacks 18 = delta) (hl : a.stacks 13 = limit)
    (hz : a.stacks 3 = zero) (ho : a.stacks 10 = one)
    (h14 : a.stacks 14 = []) (h17 : a.stacks 17 = []) (h31 : a.stacks 31 = []) :
    ∃ b : Data, RunsIn program (bound t width rowWidth positions delta limit zero one)
      (a.withPC (some program.entry)) (b.withPC none) ∧
      b.stacks = Function.update (Function.update a.stacks 18 []) 31
        (UniversalRowProgram.rowCode zero one (zero ++ one)
          (UniversalRowDataProgram.row t positions delta limit)) := by
  obtain ⟨nd, hnd, middle, hdata, hm⟩ := UniversalRowDataProgram.command_eval t width rowWidth
    positions valid delta limit a ha hd hl h14 h17 h31
  obtain ⟨ne, hne, hem⟩ := UniversalRowEmitCall.command_eval middle zero one
    (UniversalRowDataProgram.row t positions delta limit)
    (by simp [hm]) (by simpa [hm] using hz) (by simpa [hm] using ho)
    (by simpa [hm] using ha.empty 1 (by simp))
    (by simpa [hm] using ha.empty 2 (by simp))
    (by simpa [hm] using ha.empty 4 (by simp))
    (by simpa [hm] using ha.empty 5 (by simp))
    (by simpa [hm] using ha.empty 6 (by simp))
  refine ⟨_, ⟨nd + ne + 1, ?_, compiled_halt_trace (hdata.seq hem) 31 31⟩, ?_⟩
  · unfold bound
    omega
  · simp [UniversalRowEmitCall.result, hm]

theorem primitive_run (t : Tables) (width rowWidth : Word) (positions : List ℕ)
    (valid : Valid t width rowWidth positions) (delta limit zero one : Word) (a : Data)
    (ha : ready t width rowWidth positions a)
    (hd : a.stacks 18 = delta) (hl : a.stacks 13 = limit)
    (hz : a.stacks 3 = zero) (ho : a.stacks 10 = one)
    (h14 : a.stacks 14 = []) (h17 : a.stacks 17 = []) (h31 : a.stacks 31 = []) :
    ∃ b : Data, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * bound t width rowWidth positions delta limit zero one)
      (BitProgram.primitiveCfg program (a.withPC (some program.entry)))
      (BitProgram.primitiveCfg program (b.withPC none)) ∧
      b.stacks = Function.update (Function.update a.stacks 18 []) 31
        (UniversalRowProgram.rowCode zero one (zero ++ one)
          (UniversalRowDataProgram.row t positions delta limit)) := by
  obtain ⟨b, hb, hs⟩ := program_runsIn t width rowWidth positions valid delta limit zero one a
    ha hd hl hz ho h14 h17 h31
  exact ⟨b, BitProgram.primitive_execution program hb, hs⟩

end SubexponentialSAT.Subexp.UniversalRowSourceProgram

end OAI.Algorithms
