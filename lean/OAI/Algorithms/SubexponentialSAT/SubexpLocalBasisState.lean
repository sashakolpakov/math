import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLocalBasisPrepare
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchState

namespace OAI.Algorithms

/-! Exact states for physical counter preparation and batch cleanup. -/

namespace SubexponentialSAT.SubexpLocalBasisState

open BitProgram StructuredCalls

abbrev Data := State 32 131
abbrev Context := Subexp.LocalBasisBatchProgram.Context

def unary (bits : List Bool) : List Bool :=
  List.replicate (CounterPrograms.value bits) true

def derived (ctx : Context) (bits : List Bool) : Context := { ctx with length := unary bits }

def extendState (d : State 32 128) (counter left right : List Bool) : Data :=
  ⟨d.regs, Fin.addCases (m := 128) (n := 3) (motive := fun _ => List Bool)
    d.stacks ![counter, left, right]⟩

def ready (ctx : Context) (regs : Fin 32 → Bool) (counter old : List Bool) : Data :=
  extendState ⟨regs, Function.update
    (Subexp.LocalBasisBatchProgram.inputState ctx regs).stacks 127 old⟩ counter [] []

def prepared (ctx : Context) (regs : Fin 32 → Bool) (counter : List Bool) : Data :=
  extendState (Subexp.LocalBasisBatchProgram.inputState (derived ctx counter) regs) counter [] []

def afterBatch (ctx : Context) (regs : Fin 32 → Bool)
    (counter width result : List Bool) : Data :=
  extendState (Subexp.LocalBasisBatchProgram.outputState (derived ctx counter) width result regs)
    counter [] []

def result (ctx : Context) (counter output : List Bool) : Data :=
  extendState (Subexp.LocalBasisBatchProgram.outputState {ctx with length := []} [] output
    (fun _ => false)) counter [] []

theorem extend_update (regs : Fin 32 → Bool) (cells : Fin 128 → List Bool)
    (counter left right : List Bool)
    (i : Fin 128) (bits : List Bool) :
    (extendState ⟨regs, Function.update cells i bits⟩ counter left right).stacks =
      Function.update (extendState ⟨regs, cells⟩ counter left right).stacks (i.castAdd 3) bits := by
  funext j
  refine Fin.addCases (m := 128) (n := 3) (fun k => ?_) (fun k => ?_) j
  · by_cases hk : k = i
    · subst k; simp [extendState]
    · have hki : k.castAdd 3 ≠ i.castAdd 3 := by
        intro h
        exact hk (Fin.ext (congrArg (fun q : Fin 131 => q.val) h))
      simp only [extendState, Fin.addCases_left, Function.update_of_ne hk,
        Function.update_of_ne hki]
  · have hki : k.natAdd 128 ≠ i.castAdd 3 := by
      intro h
      have hv := congrArg (fun q : Fin 131 => q.val) h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    simp only [extendState, Fin.addCases_right, Function.update_of_ne hki]

theorem input_length (ctx : Context) (regs : Fin 32 → Bool) (bits : List Bool) :
    (Subexp.LocalBasisBatchProgram.inputState {ctx with length := bits} regs).stacks =
      Function.update (Subexp.LocalBasisBatchProgram.inputState ctx regs).stacks 111 bits := by
  funext i
  by_cases hi : i = 111
  · subst i; simp [Subexp.LocalBasisBatchProgram.inputState]
  · simp [Subexp.LocalBasisBatchProgram.inputState, hi]

theorem prepared_stacks (ctx : Context) (regs : Fin 32 → Bool) (counter old : List Bool) :
    (prepared ctx regs counter).stacks =
      Function.update (Function.update (ready ctx regs counter old).stacks 127 []) 111
        (unary counter) := by
  have h127 : (extendState (Subexp.LocalBasisBatchProgram.inputState ctx regs)
      counter [] []).stacks 127 = [] := by
    simp [extendState, Subexp.LocalBasisBatchProgram.inputState,
      Fin.addCases, Fin.coe_ofNat_eq_mod]
  have hbase : Function.update
      (extendState (Subexp.LocalBasisBatchProgram.inputState ctx regs) counter [] []).stacks
      127 [] = (extendState (Subexp.LocalBasisBatchProgram.inputState ctx regs)
        counter [] []).stacks := by
    rw [← h127]
    exact Function.update_eq_self _ _
  unfold prepared derived ready
  rw [show Subexp.LocalBasisBatchProgram.inputState { ctx with length := unary counter } regs =
      ⟨regs, Function.update (Subexp.LocalBasisBatchProgram.inputState ctx regs).stacks
        111 (unary counter)⟩ from congrArg (StructuredProgram.State.mk regs)
          (input_length ctx regs (unary counter))]
  rw [extend_update, extend_update]
  simp only [show ((127 : Fin 128).castAdd 3 : Fin 131) = 127 from rfl,
    show ((111 : Fin 128).castAdd 3 : Fin 131) = 111 from rfl,
    Function.update_idem]
  exact congrArg (fun f => Function.update f (111 : Fin 131) (unary counter)) hbase.symm

def prepareBound (ctx : Context) (counter old : List Bool) : ℕ :=
  2 * ctx.length.length + 2 * old.length + 7 * counter.length +
    CounterConversions.runtimeBound counter + 11

theorem prepare_ready (ctx : Context) (regs : Fin 32 → Bool) (counter old : List Bool) :
    ∃ n rf, n ≤ prepareBound ctx counter old ∧
      Eval SubexpLocalBasisPrepare.prepare n (ready ctx regs counter old)
        (prepared ctx rf counter) := by
  obtain ⟨n, e, hn, he, hs⟩ := SubexpLocalBasisPrepare.prepare_eval
    (ready ctx regs counter old) (by rfl) (by rfl)
  have hcounter : (ready ctx regs counter old).stacks 128 = counter := rfl
  rw [hcounter] at hs
  have hready : (ready ctx e.regs counter old).stacks =
      (ready ctx regs counter old).stacks := rfl
  have hout : e = prepared ctx e.regs counter := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · rw [prepared_stacks ctx e.regs counter old]
      rw [hready]
      simpa only [unary] using hs
  refine ⟨n, e.regs, ?_, hout ▸ he⟩
  simpa [SubexpLocalBasisPrepare.prepareCost, prepareBound, ready, extendState,
    Subexp.LocalBasisBatchProgram.inputState, Fin.addCases, Fin.coe_ofNat_eq_mod] using hn

theorem finished_afterBatch (ctx : Context) (regs : Fin 32 → Bool)
    (counter width output : List Bool) :
    SubexpLocalBasisPrepare.finished (afterBatch ctx regs counter width output) =
      result ctx counter output := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · unfold SubexpLocalBasisPrepare.finished afterBatch result
    simp only [Subexp.LocalBasisBatchProgram.outputState]
    rw [extend_update, extend_update, extend_update, extend_update]
    funext i
    refine Fin.addCases (m := 128) (n := 3) (fun j => ?_) (fun j => ?_) i
    · by_cases hj111 : j = 111
      · subst j
        simp [extendState, Subexp.LocalBasisBatchProgram.inputState, derived,
          Fin.addCases, Fin.coe_ofNat_eq_mod]
      by_cases hj114 : j = 114
      · subst j; simp
      by_cases hj127 : j = 127
      · subst j; simp
      have hcast (q : Fin 128) (h : j ≠ q) : j.castAdd 3 ≠ q.castAdd 3 := by
        intro he
        exact h (Fin.ext (congrArg (fun t : Fin 131 => t.val) he))
      have h111 := hcast 111 hj111
      have h114 := hcast 114 hj114
      have h127 := hcast 127 hj127
      simp only [show ((127 : Fin 128).castAdd 3 : Fin 131) = 127 from rfl,
        show ((114 : Fin 128).castAdd 3 : Fin 131) = 114 from rfl,
        show ((111 : Fin 128).castAdd 3 : Fin 131) = 111 from rfl] at h111 h114 h127 ⊢
      simp only [Function.update_of_ne h111, Function.update_of_ne h114,
        Function.update_of_ne h127, extendState, Fin.addCases_left]
      simp [Subexp.LocalBasisBatchProgram.inputState, derived, hj111]
    · fin_cases j <;> simp [extendState, Fin.addCases, Fin.coe_ofNat_eq_mod]

theorem finish_batch (ctx : Context) (regs : Fin 32 → Bool)
    (counter width output : List Bool) :
    Eval SubexpLocalBasisPrepare.finish
      (2 * CounterPrograms.value counter + 2 * width.length + 38)
      (afterBatch ctx regs counter width output) (result ctx counter output) := by
  have h := SubexpLocalBasisPrepare.finish_eval (afterBatch ctx regs counter width output)
  rw [finished_afterBatch] at h
  simpa [SubexpLocalBasisPrepare.finishCost, afterBatch, extendState,
    Subexp.LocalBasisBatchProgram.outputState, Subexp.LocalBasisBatchProgram.inputState,
    derived, unary, Fin.addCases, Fin.coe_ofNat_eq_mod] using h

end SubexponentialSAT.SubexpLocalBasisState

end OAI.Algorithms
