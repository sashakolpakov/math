import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLocalBasisState
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchProgram

namespace OAI.Algorithms

/-! The fixed batch wrapper: derive R, execute the native batch, and clean up. -/

namespace SubexponentialSAT.SubexpLocalBasisControl

open BitProgram StructuredCalls SubexpLocalBasisState

def nativePorts : Fin 128 → Fin 131 := Fin.castAdd 3

theorem nativePorts_injective : Function.Injective nativePorts := by
  intro i j h
  exact Fin.ext (congrArg (fun q : Fin 131 => q.val) h)

theorem embed_native (frame lower : State 32 128) (counter left right : List Bool) :
    embedState id nativePorts (extendState frame counter left right) lower =
      extendState lower counter left right := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id nativePorts_injective
  · intro i; rfl
  · intro i hi
    exact False.elim (hi ⟨i, rfl⟩)
  · intro i
    simp only [extendState, nativePorts, Fin.addCases_left]
  · intro i hi
    revert hi
    refine Fin.addCases (m := 128) (n := 3) (fun j => ?_) (fun j => ?_) i
    · intro hj
      exact False.elim (hj ⟨j, rfl⟩)
    · intro _
      simp only [extendState, Fin.addCases_right]

abbrev nativeCall : Cmd 32 131 := .call (ProgramLinking.liftProgram
  Subexp.LocalBasisBatchProgram.program id nativePorts)

abbrev command : Cmd 32 131 := .seq SubexpLocalBasisPrepare.prepare
  (.seq nativeCall SubexpLocalBasisPrepare.finish)

def program := compiled command 128 127

theorem nativeCall_eval (ctx : Context) (regs rf : Fin 32 → Bool)
    (counter width output : List Bool) (n : ℕ)
    (ht : Trace Subexp.LocalBasisBatchProgram.program n
      ((Subexp.LocalBasisBatchProgram.inputState (derived ctx counter) regs).withPC
        (some Subexp.LocalBasisBatchProgram.program.entry))
      ((Subexp.LocalBasisBatchProgram.outputState (derived ctx counter) width output rf).withPC none)) :
    Eval nativeCall n (prepared ctx regs counter) (afterBatch ctx rf counter width output) := by
  have he := eval_call_lifted Subexp.LocalBasisBatchProgram.program id nativePorts
    (prepared ctx regs counter) Function.injective_id nativePorts_injective ht
  simpa only [prepared, afterBatch, embed_native] using he

def bound (ctx : Context) (counter old width : List Bool) (nativeBound : ℕ) : ℕ :=
  prepareBound ctx counter old + nativeBound + 2 * CounterPrograms.value counter +
    2 * width.length + 39

/-- All wrapper overhead is explicit in the actual stored word lengths and
the decoded counter; no parameter-dependent constant is hidden here. -/
theorem bound_eq (ctx : Context) (counter old width : List Bool) (nativeBound : ℕ) :
    bound ctx counter old width nativeBound =
      nativeBound + 32 * (CounterPrograms.value counter + 1) * (counter.length + 1) +
        7 * counter.length + 2 * CounterPrograms.value counter +
        2 * ctx.length.length + 2 * old.length + 2 * width.length + 50 := by
  unfold bound prepareBound CounterConversions.runtimeBound
  omega

/-- Composition at the exact native-program boundary. The final Main theorem
must obtain these traces from the concrete batch implementation. -/
theorem program_runs_of_native (ctx : Context) (counter old width output : List Bool)
    (regs : Fin 32 → Bool) (nativeBound : ℕ)
    (hnative : ∀ rr : Fin 32 → Bool, ∃ rf,
      RunsIn Subexp.LocalBasisBatchProgram.program nativeBound
        ((Subexp.LocalBasisBatchProgram.inputState (derived ctx counter) rr).withPC
          (some Subexp.LocalBasisBatchProgram.program.entry))
        ((Subexp.LocalBasisBatchProgram.outputState (derived ctx counter) width output rf).withPC none)) :
    RunsIn program (bound ctx counter old width nativeBound)
      ((ready ctx regs counter old).withPC (some program.entry))
      ((result ctx counter output).withPC none) := by
  obtain ⟨np, rp, hp, hep⟩ := prepare_ready ctx regs counter old
  obtain ⟨rf, nn, hn, htn⟩ := hnative rp
  have hen := nativeCall_eval ctx rp rf counter width output nn htn
  have hef := finish_batch ctx rf counter width output
  have he := hep.seq (hen.seq hef)
  refine ⟨_, ?_, compiled_halt_trace he 128 127⟩
  unfold bound
  omega

/-- The native search may return its witnesses after seeing the actual entry
register state. This form preserves their checked semantic property. -/
theorem program_runs_exists {α : Type} (encode : α → List Bool) (Good : α → Prop)
    (ctx : Context) (counter old width : List Bool) (regs : Fin 32 → Bool) (nativeBound : ℕ)
    (hnative : ∀ rr : Fin 32 → Bool, ∃ x rf, Good x ∧
      RunsIn Subexp.LocalBasisBatchProgram.program nativeBound
        ((Subexp.LocalBasisBatchProgram.inputState (derived ctx counter) rr).withPC
          (some Subexp.LocalBasisBatchProgram.program.entry))
        ((Subexp.LocalBasisBatchProgram.outputState (derived ctx counter) width (encode x) rf).withPC none)) :
    ∃ x, Good x ∧ RunsIn program (bound ctx counter old width nativeBound)
      ((ready ctx regs counter old).withPC (some program.entry))
      ((result ctx counter (encode x)).withPC none) := by
  obtain ⟨np, rp, hp, hep⟩ := prepare_ready ctx regs counter old
  obtain ⟨x, rf, hx, nn, hn, htn⟩ := hnative rp
  have hen := nativeCall_eval ctx rp rf counter width (encode x) nn htn
  have hef := finish_batch ctx rf counter width (encode x)
  have he := hep.seq (hen.seq hef)
  refine ⟨x, hx, _, ?_, compiled_halt_trace he 128 127⟩
  unfold bound
  omega

end SubexponentialSAT.SubexpLocalBasisControl

end OAI.Algorithms
