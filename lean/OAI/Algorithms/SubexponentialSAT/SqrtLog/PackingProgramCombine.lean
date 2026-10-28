import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramScale
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramCounts

namespace OAI.Algorithms

/-! A fixed two-call score combiner. Inputs are binary weights and canonical
false-unary collision counts. The only modified port is the score accumulator. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

 theorem scale_lifted {R S : ℕ} (register : Fin 3 → Fin R) (stack : Fin 6 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (d : State R S) (count : ℕ)
    (hc : d.stacks (stack 1) = List.replicate count false)
    (h3 : d.stacks (stack 3) = []) (h4 : d.stacks (stack 4) = [])
    (h5 : d.stacks (stack 5) = []) :
    ∃ t ≤ scaleBudget (d.stacks (stack 0)) count+1, ∃ e : State R S,
      Eval (liftCommand scaleCommand 0 2 register stack) t d e ∧
      e.stacks (stack 2) =
        List.replicate (SubexponentialSAT.CounterPrograms.value (d.stacks (stack 0))*count) false ++
          d.stacks (stack 2) ∧
      (∀ j, j ≠ stack 2 → e.stacks j = d.stacks j) := by
  let a := projectState register stack d
  obtain ⟨t, ht, b, hb, ho, hf⟩ := scaleCommand_eval a count hc h3 h4 h5
  refine ⟨t+1, by simpa [a, projectState] using Nat.add_le_add_right ht 1,
    embedState register stack d b,
    eval_liftCommand_from_state _ 0 2 register stack d hr hs hb, ?_, ?_⟩
  · simpa [a, projectState, embedState_stack register stack d b hs 2] using ho
  · intro j hj
    by_cases hm : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hm
      rw [embedState_stack register stack d b hs i]
      exact hf i (fun h => hj (congrArg stack h))
    · exact embedState_stack_frame register stack d b j hm

abbrev CombineData := State 3 8

def incidenceScaleStacks : Fin 6 → Fin 8 := ![0,1,4,5,6,7]
def headScaleStacks : Fin 6 → Fin 8 := ![2,3,4,5,6,7]

theorem incidenceScaleStacks_injective : Function.Injective incidenceScaleStacks := by decide
theorem headScaleStacks_injective : Function.Injective headScaleStacks := by decide

abbrev combineCommand : Cmd 3 8 :=
  .seq (liftCommand scaleCommand 0 2 id incidenceScaleStacks)
    (liftCommand scaleCommand 0 2 id headScaleStacks)
def combineProgram := compiled combineCommand 0 4

def combineBudget (d : CombineData) (ci ch : ℕ) :=
  scaleBudget (d.stacks 0) ci + scaleBudget (d.stacks 2) ch + 2

 theorem combineCommand_eval (d : CombineData) (ci ch : ℕ)
    (hi : d.stacks 1 = List.replicate ci false)
    (hh : d.stacks 3 = List.replicate ch false)
    (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) :
    ∃ t ≤ combineBudget d ci ch, ∃ e : CombineData,
      Eval combineCommand t d e ∧
      e.stacks 4 = List.replicate
        (SubexponentialSAT.CounterPrograms.value (d.stacks 0)*ci +
          SubexponentialSAT.CounterPrograms.value (d.stacks 2)*ch) false ++ d.stacks 4 ∧
      (∀ j, j ≠ 4 → e.stacks j = d.stacks j) := by
  obtain ⟨t₁, ht₁, a, ha, ho₁, hf₁⟩ := scale_lifted id incidenceScaleStacks
    Function.injective_id incidenceScaleStacks_injective d ci hi h5 h6 h7
  have hha : a.stacks 3 = List.replicate ch false := (hf₁ 3 (by decide)).trans hh
  have ha5 : a.stacks 5 = [] := (hf₁ 5 (by decide)).trans h5
  have ha6 : a.stacks 6 = [] := (hf₁ 6 (by decide)).trans h6
  have ha7 : a.stacks 7 = [] := (hf₁ 7 (by decide)).trans h7
  obtain ⟨t₂, ht₂, e, he, ho₂, hf₂⟩ := scale_lifted id headScaleStacks
    Function.injective_id headScaleStacks_injective a ch hha ha5 ha6 ha7
  have ha2 : a.stacks 2 = d.stacks 2 := hf₁ 2 (by decide)
  refine ⟨t₁+t₂, ?_, e, ha.seq he, ?_, ?_⟩
  · simp only [incidenceScaleStacks, headScaleStacks, Matrix.cons_val_zero ] at ht₁ ht₂
    change t₁ ≤ scaleBudget (d.stacks 0) ci+1 at ht₁
    change t₂ ≤ scaleBudget (a.stacks 2) ch+1 at ht₂
    rw [ha2] at ht₂
    unfold combineBudget
    omega
  · change a.stacks 4 = List.replicate (SubexponentialSAT.CounterPrograms.value (d.stacks 0)*ci) false ++ d.stacks 4 at ho₁
    change e.stacks 4 = List.replicate (SubexponentialSAT.CounterPrograms.value (a.stacks 2)*ch) false ++ a.stacks 4 at ho₂
    rw [ho₂, ha2, ho₁, ← List.append_assoc, ← List.replicate_add]
    congr 2
    omega
  · intro j hj
    exact (hf₂ j hj).trans (hf₁ j hj)

 theorem combineProgram_primitive (d : CombineData) (ci ch : ℕ)
    (hi : d.stacks 1 = List.replicate ci false)
    (hh : d.stacks 3 = List.replicate ch false)
    (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) :
    ∃ e : CombineData,
      SubexponentialSAT.Computation.RunsIn (primitive combineProgram).step
        (primitiveOverhead combineProgram * (combineBudget d ci ch+1))
        (primitiveCfg combineProgram (d.withPC (some combineProgram.entry)))
        (primitiveCfg combineProgram (e.withPC none)) ∧
      e.stacks 4 = List.replicate
        (SubexponentialSAT.CounterPrograms.value (d.stacks 0)*ci +
          SubexponentialSAT.CounterPrograms.value (d.stacks 2)*ch) false ++ d.stacks 4 ∧
      (∀ j, j ≠ 4 → e.stacks j = d.stacks j) := by
  obtain ⟨t, ht, e, he, ho, hf⟩ := combineCommand_eval d ci ch hi hh h5 h6 h7
  exact ⟨e, primitive_execution combineProgram ⟨t+1, by omega, compiled_halt_trace he 0 4⟩, ho, hf⟩

 theorem combine_lifted {R S : ℕ} (register : Fin 3 → Fin R) (stack : Fin 8 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (d : State R S) (ci ch : ℕ)
    (hi : d.stacks (stack 1) = List.replicate ci false)
    (hh : d.stacks (stack 3) = List.replicate ch false)
    (h5 : d.stacks (stack 5) = []) (h6 : d.stacks (stack 6) = [])
    (h7 : d.stacks (stack 7) = []) :
    ∃ t ≤ combineBudget (projectState register stack d) ci ch+1, ∃ e : State R S,
      Eval (liftCommand combineCommand 0 4 register stack) t d e ∧
      e.stacks (stack 4) = List.replicate
        (SubexponentialSAT.CounterPrograms.value (d.stacks (stack 0))*ci +
          SubexponentialSAT.CounterPrograms.value (d.stacks (stack 2))*ch) false ++ d.stacks (stack 4) ∧
      (∀ j, j ≠ stack 4 → e.stacks j = d.stacks j) := by
  let a := projectState register stack d
  obtain ⟨t, ht, b, hb, ho, hf⟩ := combineCommand_eval a ci ch hi hh h5 h6 h7
  refine ⟨t+1, Nat.add_le_add_right ht 1, embedState register stack d b,
    eval_liftCommand_from_state _ 0 4 register stack d hr hs hb, ?_, ?_⟩
  · simpa [a, projectState, embedState_stack register stack d b hs 4] using ho
  · intro j hj
    by_cases hm : ∃ i, stack i = j
    · obtain ⟨i, rfl⟩ := hm
      rw [embedState_stack register stack d b hs i]
      exact hf i (fun h => hj (congrArg stack h))
    · exact embedState_stack_frame register stack d b j hm
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
