import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorArithmeticProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorCacheProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorDispatchFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorID
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramExpansionForward
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorServicesBase

/-! The accepted-assignment factor product uses the original finite-ring
indicator and clause programs after the concrete specialized table producer.
Every cache is rebuilt from persistent source words by paid native copies;
neutral factor IDs leave the running multiplicative identity unchanged. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram
noncomputable section

def copy (src dst : Fin 896) : Code :=
  .call (StackRoutines.copyProgram src dst 159 0 1)

def clear (src : Fin 896) : Code := .call (StackRoutines.clearProgram src 0 1)

def cleared (a : Data) (src : Fin 896) : Data :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks src []⟩

theorem clear_eval (a : Data) (src : Fin 896) :
    Eval (clear src) (2 * (a.stacks src).length + 3) a (cleared a src) :=
  Eval.call _ (ListRegisterProgram.clear_run src (0 : Fin 40) 1 a.regs a.stacks)

def move (src dst : Fin 896) : Code := .seq (copy src dst) (clear src)

def moved (a : Data) (src dst : Fin 896) : Data :=
  ⟨readRegs a.regs 0 1 none,
    Function.update (Function.update a.stacks dst (a.stacks src ++ a.stacks dst)) src []⟩

theorem move_eval (a : Data) (src dst : Fin 896)
    (hsd : src ≠ dst) (hst : src ≠ 159) (htd : (159 : Fin 896) ≠ dst)
    (htmp : a.stacks 159 = []) :
    Eval (move src dst) (9 * (a.stacks src).length + 8) a (moved a src dst) := by
  have hcopy := SubexpScanPrimitives.copy_eval a src dst 159 0 1 hsd hst htd (by decide) htmp
  let b := SubexpScanPrimitives.afterCopy a src dst 0 1
  have hclear : Eval (clear src) (2 * (b.stacks src).length + 3) b
      ⟨readRegs b.regs 0 1 none, Function.update b.stacks src []⟩ :=
    Eval.call _ (ListRegisterProgram.clear_run src (0 : Fin 40) 1 b.regs b.stacks)
  have hlen : b.stacks src = a.stacks src := by
    simp [b, SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks, hsd]
  have hout : (⟨readRegs b.regs 0 1 none, Function.update b.stacks src []⟩ : Data) =
      moved a src dst := by
    apply congrArg₂ StructuredProgram.State.mk
    · simp [b, SubexpScanPrimitives.afterCopy, StackRoutines.readRegs_reset]
    · rfl
  rw [hout] at hclear
  have he := hcopy.seq hclear
  simpa only [move, copy, hlen, show 7 * (a.stacks src).length + 5 +
    (2 * (a.stacks src).length + 3) = 9 * (a.stacks src).length + 8 by omega] using he

/-- Only transient arithmetic, parser and source-worker storage is cleared.
The current record149, pending records150 and running product151 remain live. -/
def callbackScratch : List (Fin 768) :=
  List.map Factor.indicatorStacks FactorServices.indicatorScratch ++
    [62, 64, 159, 556] ++ FactorDispatch.scratch ++ Expansion.scratch ++ [358]

def clearCallbackLocal : Cmd 16 768 := clearMany callbackScratch

def clearCallback : Code := liftCommand clearCallbackLocal 149 149 localRegister lowStack

noncomputable def callbackInitial (a : Data) : Data :=
  embedState localRegister lowStack a
    (clearManyState callbackScratch (projectState localRegister lowStack a))

def clearCallbackCost (a : Data) : ℕ :=
  clearManyCost callbackScratch (projectState localRegister lowStack a) + 1

theorem clearCallback_eval (a : Data) :
    Eval clearCallback (clearCallbackCost a) a (callbackInitial a) :=
  eval_liftCommand_from_state clearCallbackLocal 149 149 localRegister lowStack a
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _)
    (clearMany_eval callbackScratch (projectState localRegister lowStack a))

theorem callbackInitial_low (a : Data) (i : Fin 768) :
    (callbackInitial a).stacks (lowStack i) =
      if i ∈ callbackScratch then [] else a.stacks (lowStack i) := by
  exact (embedState_stack localRegister lowStack a
    (clearManyState callbackScratch (projectState localRegister lowStack a))
    (Fin.castAdd_injective _ _) i).trans
    (clearMany_stacks callbackScratch (projectState localRegister lowStack a) i)

theorem callbackInitial_frame (a : Data) (i : Fin 896)
    (hi : i ∉ callbackScratch.map lowStack) :
    (callbackInitial a).stacks i = a.stacks i := by
  by_cases hlt : i.val < 768
  · let j : Fin 768 := ⟨i.val, hlt⟩
    have hj : lowStack j = i := Fin.ext rfl
    have hn : j ∉ callbackScratch := by
      intro hm
      exact hi (List.mem_map.mpr ⟨j, hm, hj⟩)
    rw [← hj, callbackInitial_low, ite_eq_right hn]
  · apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega

theorem callbackInitial_wordBound (a : Data) (P : ℕ) (ha : WordBound P a) :
    WordBound P (callbackInitial a) := by
  intro i
  by_cases hi : i ∈ callbackScratch.map lowStack
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    rw [callbackInitial_low, ite_eq_left hj]
    simp
  · rw [callbackInitial_frame a i hi]
    exact ha i

theorem clearCallbackCost_le (a : Data) (P : ℕ) (ha : WordBound P a) :
    clearCallbackCost a ≤ callbackScratch.length * (2 * P + 3) + 1 :=
  Nat.add_le_add_right
    (clearManyCost_le callbackScratch (projectState localRegister lowStack a) P
      (fun i => ha (lowStack i))) 1

def prepareIncidence : Code :=
  .seq (liftLow FactorID.command 149 556) FactorTableProgram.caller

def hashFactor : Code := .seq prepareIncidence
  (liftLow (.seq Expansion.forwardCommand FactorEvaluationSpace.hashArithmetic) 154 151)

def markedFactor : Code := .seq prepareIncidence
  (liftLow (.seq (Factor.move 154 63) FactorEvaluationSpace.markedArithmetic) 154 151)

def choose : Code := .ite 5 hashFactor (.ite 6 markedFactor (.base .skip))

def returnToRecords : Code :=
  .seq (.base (.atom (.set 13 false)))
    (.seq (.base (.atom (.set 14 true))) (.base (.atom (.set 15 false))))

def returned (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 13 false) 14 true) 15 false,
    a.stacks⟩

theorem returnToRecords_eval (a : Data) : Eval returnToRecords 3 a (returned a) := by
  let b : Data := ⟨Function.update a.regs 13 false, a.stacks⟩
  let c : Data := ⟨Function.update b.regs 14 true, a.stacks⟩
  have h1 : Eval (.base (.atom (.set 13 false))) 1 a b := .base (.atom _ _)
  have h2 : Eval (.base (.atom (.set 14 true))) 1 b c := .base (.atom _ _)
  have h3 : Eval (.base (.atom (.set 15 false))) 1 c (returned a) := .base (.atom _ _)
  exact h1.seq (h2.seq h3)

def callbackFinished (a : Data) : Data := returned (cleared a 149)

theorem callbackFinish_eval (a : Data) :
    Eval (.seq (clear 149) returnToRecords) (2 * (a.stacks 149).length + 6)
      a (callbackFinished a) := by
  convert (clear_eval a 149).seq (returnToRecords_eval (cleared a 149)) using 1
  rfl

def ports : RecordPrograms.Ports 40 896 :=
  ⟨13, 14, 15, 150, 149, by decide, by decide, by decide, by decide⟩

def callback : Code := .seq clearCallback
  (.seq (liftLow FactorDispatch.command 149 154)
    (.seq choose (.seq (clear 149) returnToRecords)))

/-- Neutral IDs execute the dispatcher and record cleanup, retaining the
running product. No incidence lookup or arithmetic branch is executed. -/
theorem callback_neutral_eval (a : Data) (rows clauses : List (List Bool))
    (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701 = Encoding.encodeList id rows)
    (hclauses : a.stacks 700 = Encoding.encodeList id clauses)
    (hcount : a.stacks 704 = List.replicate rows.length true)
    (hmark : a.stacks 705 = Encoding.encodeNat mark)
    (hflag : a.stacks 706 = [marked])
    (hfactor : a.stacks 149 = (Encoding.encodeNat factor).reverse)
    (hvalid : marked = true → mark < clauses.length)
    (hhash : ¬factor < rows.length)
    (hmarked : (marked && decide (factor = rows.length)) = false) :
    ∃ steps b, steps ≤ clearCallbackCost a + 9 * (a.stacks 149).length + 15 +
        LeafFactorDispatchProgram.budget rows clauses mark factor ∧
      Eval callback steps a b ∧
      b.stacks = Function.update (callbackInitial a).stacks 149 [] ∧
      b.regs 13 = false ∧ b.regs 14 = true ∧ b.regs 15 = false := by
  let c := callbackInitial a
  let low := projectState id lowStack c
  have frame (i : Fin 768) (hi : i ∉ callbackScratch) : low.stacks i = a.stacks (lowStack i) := by
    exact (callbackInitial_low a i).trans (ite_eq_right hi)
  have hr : low.stacks 701 = Encoding.encodeList id rows := (frame 701 (by decide)).trans hrows
  have hc : low.stacks 700 = Encoding.encodeList id clauses := (frame 700 (by decide)).trans hclauses
  have hn : low.stacks 704 = List.replicate rows.length true := (frame 704 (by decide)).trans hcount
  have hm : low.stacks 705 = Encoding.encodeNat mark := (frame 705 (by decide)).trans hmark
  have hf : low.stacks 706 = [marked] := (frame 706 (by decide)).trans hflag
  have hid : low.stacks 149 = (Encoding.encodeNat factor).reverse := (frame 149 (by decide)).trans hfactor
  have hwork : ∀ i ∈ FactorDispatch.scratch, low.stacks i = [] := by
    intro i hi
    have hmem : i ∈ callbackScratch := by
      simp only [callbackScratch, List.mem_append]
      exact Or.inl (Or.inl (Or.inr hi))
    exact (callbackInitial_low a i).trans (ite_eq_left hmem)
  obtain ⟨kd, rd, hkd, hd, h5, h6, h7⟩ :=
    FactorDispatch.command_eval low rows clauses marked mark factor hr hc hn hm hf hid hwork hvalid
  let out := FactorDispatch.finished low rd rows clauses marked mark factor
  let wide := embedState id lowStack c out
  have hdispatch : Eval (liftLow FactorDispatch.command 149 154) (kd + 1) c wide :=
    eval_liftCommand_from_state FactorDispatch.command 149 154 id lowStack c
      Function.injective_id (Fin.castAdd_injective _ _) hd
  have hwide5 : wide.regs 5 = false := by
    rw [show wide.regs 5 = out.regs 5 from
      embedState_register id lowStack c out Function.injective_id 5]
    rw [FactorDispatch.finished_role_hash, h5]
    exact decide_eq_false hhash
  have hwide6 : wide.regs 6 = false := by
    rw [show wide.regs 6 = out.regs 6 from
      embedState_register id lowStack c out Function.injective_id 6]
    rw [FactorDispatch.finished_role_marked, h6, hmarked]
  have hpayload : LeafFactorDispatchProgram.selectedPayload rows clauses marked mark factor = [] := by
    simp [LeafFactorDispatchProgram.selectedPayload, hhash, hmarked]
  have hlow : out.stacks = low.stacks := by
    rw [FactorDispatch.finished_stacks low rd rows clauses marked mark factor hr hc hn hm hwork,
      hpayload]
    exact Function.update_eq_self_iff.mpr (hwork 154 (by decide)).symm
  have hwide : wide.stacks = c.stacks := by
    funext i
    by_cases hi : i.val < 768
    · let j : Fin 768 := ⟨i.val, hi⟩
      have hj : lowStack j = i := Fin.ext rfl
      rw [← hj, embedState_stack id lowStack c out (Fin.castAdd_injective _ _) j, hlow]
      rfl
    · apply embedState_stack_frame
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      change j.val = i.val at hv
      omega
  have hchoose : Eval choose 2 wide wide :=
    Eval.ite_false hwide5 (Eval.ite_false hwide6 (Eval.base (StructuredProgram.Eval.skip wide)))
  refine ⟨clearCallbackCost a + ((kd + 1) + (2 + (2 * (wide.stacks 149).length + 6))),
    callbackFinished wide, ?_, (clearCallback_eval a).seq (hdispatch.seq
      (hchoose.seq (callbackFinish_eval wide))), ?_, ?_, ?_, ?_⟩
  · have h149 : wide.stacks 149 = a.stacks 149 := by
      rw [hwide]
      exact callbackInitial_frame a 149 (by decide)
    have hl149 : low.stacks 149 = a.stacks 149 := frame 149 (by decide)
    rw [h149]
    rw [hl149] at hkd
    omega
  · exact congrArg (fun (store : Fin 896 → List Bool) => Function.update store 149 []) hwide
  all_goals simp [callbackFinished, returned]

def loop : Code := RecordPrograms.iterate ports callback

def emptyLoopResult (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 15 false) 13 false) 14 true,
    Function.update a.stacks 150 []⟩

/-- Even an empty factor list executes its actual terminating tag. The
running product151 remains the encoded identity generated during setup. -/
theorem loop_empty_eval (a : Data) (hsource : a.stacks 150 = [false]) :
    Eval loop 3 a (emptyLoopResult a) := by
  let a1 : Data := ⟨Function.update a.regs 15 false, a.stacks⟩
  have hs : Eval (.base (.atom (.set (15 : Fin 40) false))) 1 a a1 :=
    Eval.base (StructuredProgram.Eval.atom _ _)
  have hp := Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.pop (150 : Fin 896) (13 : Fin 40) 14) a1)
  have he : (StructuredProgram.Atom.pop (150 : Fin 896) (13 : Fin 40) 14).eval a1 =
      emptyLoopResult a := by
    simp [a1, emptyLoopResult, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, hsource,
      readRegs]
  rw [he] at hp
  have hwhile : Eval (RecordPrograms.loop ports callback) 1 (emptyLoopResult a) (emptyLoopResult a) :=
    Eval.while_false (by simp [emptyLoopResult, ports])
  exact hs.seq (hp.seq hwhile)

/-- Factor IDs are an explicitly stored polynomial-size input list. No head
assignment Cartesian product is materialized by this native record traversal. -/
def product : Code := .seq (copy 175 150)
  (.seq (copy 69 151) (.seq loop (move 151 854)))

/-- A group with no factor IDs emits the actual staged ring identity. The
empty record tag is consumed, and the full output word is copied to854. -/
theorem product_empty_eval (a : Data) (hids : a.stacks 175 = [false])
    (h150 : a.stacks 150 = []) (h151 : a.stacks 151 = [])
    (h159 : a.stacks 159 = []) (h854 : a.stacks 854 = []) :
    ∃ b, Eval product (16 * (a.stacks 69).length + 28) a b ∧
      b.stacks = Function.update (Function.update (Function.update a.stacks 150 []) 151 [])
        854 (a.stacks 69) := by
  let a1 := SubexpScanPrimitives.afterCopy a 175 150 0 1
  let a2 := SubexpScanPrimitives.afterCopy a1 69 151 0 1
  let a3 := emptyLoopResult a2
  have h1 := SubexpScanPrimitives.copy_eval a 175 150 159 0 1
    (by decide) (by decide) (by decide) (by decide) h159
  have ht1 : a1.stacks 159 = [] := by
    simp [a1, SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks, h159]
  have h2 := SubexpScanPrimitives.copy_eval a1 69 151 159 0 1
    (by decide) (by decide) (by decide) (by decide) ht1
  have hsrc : a2.stacks 150 = [false] := by
    simp [a2, a1, SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks, h150, hids]
  have h3 := loop_empty_eval a2 hsrc
  have ht3 : a3.stacks 159 = [] := by
    simp [a3, emptyLoopResult, a2, a1, SubexpScanPrimitives.afterCopy,
      StackRoutines.copyStacks, h159]
  have h4 := move_eval a3 151 854 (by decide) (by decide) (by decide) ht3
  have hlen1 : a1.stacks 69 = a.stacks 69 := by
    simp [a1, SubexpScanPrimitives.afterCopy, StackRoutines.copyStacks]
  have hlen3 : a3.stacks 151 = a.stacks 69 := by
    simp [a3, emptyLoopResult, a2, a1, SubexpScanPrimitives.afterCopy,
      StackRoutines.copyStacks, h151]
  refine ⟨moved a3 151 854, ?_, ?_⟩
  · have he := h1.seq (h2.seq (h3.seq h4))
    simpa only [product, copy, move, hids, hlen1, hlen3,
      List.length_singleton,
      show 7 * 1 + 5 + (7 * (a.stacks 69).length + 5 +
        (3 + (9 * (a.stacks 69).length + 8))) =
          16 * (a.stacks 69).length + 28 by omega] using he
  · funext i
    by_cases hi150 : i = 150 <;> by_cases hi151 : i = 151 <;> by_cases hi854 : i = 854
    all_goals simp [moved, a3, emptyLoopResult, a2, a1, SubexpScanPrimitives.afterCopy,
      StackRoutines.copyStacks, hi150, hi151, hi854, h854, h151]

/-- Reclaim all private callback and relocated source storage before the
first factor. The fixed finite list excludes every live caller master. -/
def entryScratch : List (Fin 896) :=
  [149, 150, 151, 159, 854] ++ callbackScratch.map lowStack ++
    FactorTableProgram.entryPorts

def «initialize» : Code := liftCommand (clearMany entryScratch) 175 854 localRegister id

noncomputable def initialized (a : Data) : Data :=
  embedState localRegister id a
    (clearManyState entryScratch (projectState localRegister id a))

def initializeCost (a : Data) : ℕ :=
  clearManyCost entryScratch (projectState localRegister id a) + 1

theorem initialize_eval (a : Data) :
    Eval «initialize» (initializeCost a) a (initialized a) :=
  eval_liftCommand_from_state (clearMany entryScratch) 175 854 localRegister id a
    (Fin.castAdd_injective _ _) Function.injective_id
    (clearMany_eval entryScratch (projectState localRegister id a))

theorem initialized_stacks (a : Data) (i : Fin 896) :
    (initialized a).stacks i = if i ∈ entryScratch then [] else a.stacks i := by
  exact (embedState_stack localRegister id a
    (clearManyState entryScratch (projectState localRegister id a))
    Function.injective_id i).trans (clearMany_stacks entryScratch
      (projectState localRegister id a) i)

theorem initialized_wordBound (a : Data) (P : ℕ) (ha : WordBound P a) :
    WordBound P (initialized a) := by
  intro i
  rw [initialized_stacks]
  split_ifs
  · simp
  · exact ha i

theorem initializeCost_le (a : Data) (P : ℕ) (ha : WordBound P a) :
    initializeCost a ≤ entryScratch.length * (2 * P + 3) + 1 :=
  Nat.add_le_add_right
    (clearManyCost_le entryScratch (projectState localRegister id a) P ha) 1

/-- A single accepted ambient assignment145 is evaluated. The complete group
product is placed on854 for the head-sum addition; the arithmetic environment
remains installed for that addition. -/
def assignment : Code := .seq «initialize» (.seq setup product)

def program := compiled assignment 175 854

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentProgram
