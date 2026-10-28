import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-! A fixed binary-counted copier scales a unary score, preserving both inputs.
The loop count is read from the multiplier stack and every copied bit is paid. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev ScaleData := SubexponentialSAT.StructuredProgram.State 3 6

def scalePorts : SubexponentialSAT.CounterForPrograms.Ports 3 6 where
  register := Function.Embedding.refl _
  counter := 3
  scratch := 4
  counter_ne_scratch := by decide

abbrev scaleCopy (src dst : Fin 6) : Cmd 3 6 :=
  .call (SubexponentialSAT.StackRoutines.copyProgram src dst 5 0 1)
abbrev scaleClear : Cmd 3 6 := .call (SubexponentialSAT.StackRoutines.clearProgram 3 0 1)
abbrev scaleCommand : Cmd 3 6 :=
  .seq (scaleCopy 0 3)
    (.seq (SubexponentialSAT.CounterForPrograms.forCmd scalePorts (scaleCopy 1 2)) scaleClear)
def scaleProgram := compiled scaleCommand 0 2

def scaleInvariant (base : ScaleData) (count : ℕ) (i : ℕ) (d : ScaleData) : Prop :=
  d.stacks 1 = List.replicate count false ∧
  d.stacks 2 = List.replicate (i*count) false ++ base.stacks 2 ∧
  d.stacks 5 = [] ∧
  (∀ j : Fin 6, j ≠ 2 → j ≠ 3 → j ≠ 4 → d.stacks j = base.stacks j)

 theorem scaleInvariant_stable (base : ScaleData) (count : ℕ) :
    SubexponentialSAT.CounterForPrograms.FrameStable scalePorts (scaleInvariant base count) := by
  intro i a b hab ha
  refine ⟨(hab 1 (by decide) (by decide)).symm.trans ha.1,
    (hab 2 (by decide) (by decide)).symm.trans ha.2.1,
    (hab 5 (by decide) (by decide)).symm.trans ha.2.2.1, ?_⟩
  intro j hj2 hj3 hj4
  exact (hab j hj3 hj4).symm.trans (ha.2.2.2 j hj2 hj3 hj4)

 theorem scale_body_spec (base : ScaleData) (count : ℕ) :
    SubexponentialSAT.CounterForPrograms.BodySpec scalePorts (scaleCopy 1 2)
      (scaleInvariant base count) (fun _ => 7*count+5) := by
  intro i d hi hs hv
  let e := SubexponentialSAT.SubexpScanPrimitives.afterCopy d 1 2 0 1
  have he := SubexponentialSAT.SubexpScanPrimitives.copy_eval d 1 2 5 0 1
    (by decide) (by decide) (by decide) (by decide) hi.2.2.1
  refine ⟨7*count+5, e, le_rfl, ?_, ?_, ?_, ?_⟩
  · simpa [scaleCopy, hi.1] using he
  · simp [e, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks, scalePorts]
  · simpa [e, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks, scalePorts] using hs
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [e, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks] using hi.1
    · simp only [e, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks,
        Function.update_self]
      rw [hi.1, hi.2.1, ← List.append_assoc, ← List.replicate_add]
      congr 2
      ring
    · simpa [e, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks] using hi.2.2.1
    · intro j hj2 hj3 hj4
      simpa [e, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks, hj2] using
        hi.2.2.2 j hj2 hj3 hj4

 def scaleBudget (bits : List Bool) (count : ℕ) : ℕ :=
  9*bits.length+8 + SubexponentialSAT.CounterPrograms.value bits*(7*count+5) +
    (SubexponentialSAT.CounterPrograms.value bits+1)*(16*bits.length+16)

 theorem scaleCommand_eval (d : ScaleData) (count : ℕ)
    (hcount : d.stacks 1 = List.replicate count false)
    (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = []) :
    ∃ t ≤ scaleBudget (d.stacks 0) count, ∃ e : ScaleData,
      Eval scaleCommand t d e ∧
      e.stacks 2 = List.replicate (SubexponentialSAT.CounterPrograms.value (d.stacks 0)*count) false ++ d.stacks 2 ∧
      (∀ j : Fin 6, j ≠ 2 → e.stacks j = d.stacks j) := by
  let a := SubexponentialSAT.SubexpScanPrimitives.afterCopy d 0 3 0 1
  have hcopy := SubexponentialSAT.SubexpScanPrimitives.copy_eval d 0 3 5 0 1
    (by decide) (by decide) (by decide) (by decide) h5
  have ha3 : a.stacks 3 = d.stacks 0 := by
    simp [a, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks, h3]
  have ha4 : a.stacks scalePorts.scratch = [] := by
    simpa [a, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks, scalePorts] using h4
  have hi : scaleInvariant d count 0 a := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [a, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks] using hcount
    · simp [a, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks]
    · simpa [a, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks] using h5
    · intro j hj2 hj3 hj4
      simp [a, SubexponentialSAT.SubexpScanPrimitives.afterCopy, SubexponentialSAT.StackRoutines.copyStacks, hj3]
  obtain ⟨n, b, hb, hbi, hbv, hbl, hbs, hbn⟩ :=
    SubexponentialSAT.CounterForPrograms.for_correct scalePorts (scaleCopy 1 2)
      (scaleInvariant d count) (fun _ => 7*count+5)
      (scaleInvariant_stable d count) (scale_body_spec d count) a ha4 hi
  let e : ScaleData := ⟨readRegs b.regs 0 1 none, Function.update b.stacks 3 []⟩
  have he : Eval scaleClear (2*(b.stacks 3).length+3) b e :=
    .call _ (SubexponentialSAT.ListRegisterProgram.clear_run 3 0 1 b.regs b.stacks)
  refine ⟨(7*(d.stacks 0).length+5)+(n+(2*(b.stacks 3).length+3)), ?_, e,
    hcopy.seq (hb.seq he), ?_, ?_⟩
  · have hbl' : (b.stacks 3).length = (d.stacks 0).length := by
      simpa only [scalePorts, ha3] using hbl
    have hbn' : n ≤ SubexponentialSAT.CounterPrograms.value (d.stacks 0)*(7*count+5) +
        (SubexponentialSAT.CounterPrograms.value (d.stacks 0)+1)*(16*(d.stacks 0).length+16) := by
      simpa only [scalePorts, ha3, SubexponentialSAT.CounterForPrograms.budgetSum_const] using hbn
    unfold scaleBudget
    omega
  · simpa only [e, Function.update_of_ne (by decide : (2:Fin 6) ≠ 3), scalePorts, ha3] using hbi.2.1
  · intro j hj2
    by_cases hj3 : j = 3
    · subst j; simpa [e] using h3.symm
    by_cases hj4 : j = 4
    · subst j; simpa [e, scalePorts, h4] using hbs
    · simpa [e, hj3] using hbi.2.2.2 j hj2 hj3 hj4

 theorem scaleProgram_primitive (d : ScaleData) (count : ℕ)
    (hcount : d.stacks 1 = List.replicate count false)
    (h3 : d.stacks 3 = []) (h4 : d.stacks 4 = []) (h5 : d.stacks 5 = []) :
    ∃ e : ScaleData,
      SubexponentialSAT.Computation.RunsIn (primitive scaleProgram).step
        (primitiveOverhead scaleProgram * (scaleBudget (d.stacks 0) count+1))
        (primitiveCfg scaleProgram (d.withPC (some scaleProgram.entry)))
        (primitiveCfg scaleProgram (e.withPC none)) ∧
      e.stacks 2 = List.replicate (SubexponentialSAT.CounterPrograms.value (d.stacks 0)*count) false ++ d.stacks 2 ∧
      (∀ j : Fin 6, j ≠ 2 → e.stacks j = d.stacks j) := by
  obtain ⟨t, ht, e, he, ho, hf⟩ := scaleCommand_eval d count hcount h3 h4 h5
  exact ⟨e, primitive_execution scaleProgram ⟨t+1, by omega, compiled_halt_trace he 0 2⟩, ho, hf⟩
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
