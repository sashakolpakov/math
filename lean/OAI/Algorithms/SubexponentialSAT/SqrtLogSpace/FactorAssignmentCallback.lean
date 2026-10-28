import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentLoop

/-! The actual specialized callback dispatches one stored original factor ID.
The general dispatch theorem fixes its physical payload, flags and exact frame;
hash and marked branch correctness is supplied by their concrete native proofs. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback

open OAI BitProgram StructuredCalls
open SqrtLog SqrtLog.LeafProgram MomentsProgram FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def dispatchInput (a : FactorAssignmentProgram.Data) : State 40 768 :=
  projectState id lowStack (callbackInitial a)

def dispatched (a : FactorAssignmentProgram.Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ) : FactorAssignmentProgram.Data :=
  embedState id lowStack (callbackInitial a)
    (FactorDispatch.finished (dispatchInput a) rf rows clauses marked mark factor)

/-- The paid clear preserves an already established callback boundary. -/
theorem callbackInitial_stacks (a : FactorAssignmentProgram.Data)
    (hclean : ∀ i ∈ callbackScratch, a.stacks (lowStack i) = []) :
    (callbackInitial a).stacks = a.stacks := by
  funext i
  by_cases hi : i ∈ callbackScratch.map lowStack
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    rw [callbackInitial_low, ite_eq_left hj, hclean j hj]
  · exact callbackInitial_frame a i hi

private theorem dispatchInput_frame (a : FactorAssignmentProgram.Data) (i : Fin 768)
    (hi : i ∉ callbackScratch) :
    (dispatchInput a).stacks i = a.stacks (lowStack i) :=
  (callbackInitial_low a i).trans (ite_eq_right hi)

private theorem dispatchInput_work (a : FactorAssignmentProgram.Data) :
    ∀ i ∈ FactorDispatch.scratch, (dispatchInput a).stacks i = [] := by
  intro i hi
  have hmem : i ∈ callbackScratch := by
    simp only [callbackScratch, List.mem_append]
    exact Or.inl (Or.inl (Or.inr hi))
  exact (callbackInitial_low a i).trans (ite_eq_left hmem)

/-- All caller stacks are restored except the actual selected payload154.
This frame applies to hash, marked and neutral IDs, without an early exit. -/
theorem dispatched_stacks (a : FactorAssignmentProgram.Data) (rf : Fin 8 → Bool)
    (rows clauses : List (List Bool)) (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701 = Encoding.encodeList id rows)
    (hclauses : a.stacks 700 = Encoding.encodeList id clauses)
    (hcount : a.stacks 704 = List.replicate rows.length true)
    (hmark : a.stacks 705 = Encoding.encodeNat mark) :
    (dispatched a rf rows clauses marked mark factor).stacks =
      Function.update (callbackInitial a).stacks 154
        (LeafFactorDispatchProgram.selectedPayload rows clauses marked mark factor) := by
  have hr : (dispatchInput a).stacks 701 = Encoding.encodeList id rows :=
    (dispatchInput_frame a 701 (by decide)).trans hrows
  have hc : (dispatchInput a).stacks 700 = Encoding.encodeList id clauses :=
    (dispatchInput_frame a 700 (by decide)).trans hclauses
  have hn : (dispatchInput a).stacks 704 = List.replicate rows.length true :=
    (dispatchInput_frame a 704 (by decide)).trans hcount
  have hm : (dispatchInput a).stacks 705 = Encoding.encodeNat mark :=
    (dispatchInput_frame a 705 (by decide)).trans hmark
  have hlow := FactorDispatch.finished_stacks (dispatchInput a) rf rows clauses
    marked mark factor hr hc hn hm (dispatchInput_work a)
  funext i
  by_cases hi : i.val < 768
  · let j : Fin 768 := ⟨i.val, hi⟩
    have hj : lowStack j = i := Fin.ext rfl
    rw [← hj]
    change (embedState id lowStack (callbackInitial a)
      (FactorDispatch.finished (dispatchInput a) rf rows clauses marked mark factor)).stacks
      (lowStack j) = _
    rw [embedState_stack id lowStack _ _ (Fin.castAdd_injective _ _) j, hlow]
    by_cases h154 : j = 154
    · rw [h154]
      simp [lowStack]
    · have hwide : lowStack j ≠ 154 := by
        intro he
        apply h154
        exact Fin.ext (congrArg (fun k : Fin 896 => k.val) he)
      simp only [Function.update_of_ne h154, Function.update_of_ne hwide]
      rfl
  · have h154 : i ≠ 154 := by intro he; subst i; norm_num at hi
    rw [Function.update_of_ne h154]
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega

/-- The native parser compares the complete original ID and returns both
role flags. Every copy, table scan and finite lifted return is charged. -/
theorem dispatch_eval (a : FactorAssignmentProgram.Data) (rows clauses : List (List Bool))
    (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701 = Encoding.encodeList id rows)
    (hclauses : a.stacks 700 = Encoding.encodeList id clauses)
    (hcount : a.stacks 704 = List.replicate rows.length true)
    (hmark : a.stacks 705 = Encoding.encodeNat mark)
    (hflag : a.stacks 706 = [marked])
    (hfactor : a.stacks 149 = (Encoding.encodeNat factor).reverse)
    (hvalid : marked = true → mark < clauses.length) :
    ∃ steps rf, steps ≤ 7 * (a.stacks 149).length + 7 +
        LeafFactorDispatchProgram.budget rows clauses mark factor ∧
      Eval (liftLow FactorDispatch.command 149 154) steps (callbackInitial a)
        (dispatched a rf rows clauses marked mark factor) ∧
      (dispatched a rf rows clauses marked mark factor).regs 5 =
        decide (factor < rows.length) ∧
      (dispatched a rf rows clauses marked mark factor).regs 6 =
        (marked && decide (factor = rows.length)) := by
  have hr : (dispatchInput a).stacks 701 = Encoding.encodeList id rows :=
    (dispatchInput_frame a 701 (by decide)).trans hrows
  have hc : (dispatchInput a).stacks 700 = Encoding.encodeList id clauses :=
    (dispatchInput_frame a 700 (by decide)).trans hclauses
  have hn : (dispatchInput a).stacks 704 = List.replicate rows.length true :=
    (dispatchInput_frame a 704 (by decide)).trans hcount
  have hm : (dispatchInput a).stacks 705 = Encoding.encodeNat mark :=
    (dispatchInput_frame a 705 (by decide)).trans hmark
  have hf : (dispatchInput a).stacks 706 = [marked] :=
    (dispatchInput_frame a 706 (by decide)).trans hflag
  have hid : (dispatchInput a).stacks 149 = (Encoding.encodeNat factor).reverse :=
    (dispatchInput_frame a 149 (by decide)).trans hfactor
  obtain ⟨k, rf, hk, he, h5, h6, _⟩ := FactorDispatch.command_eval
    (dispatchInput a) rows clauses marked mark factor hr hc hn hm hf hid
      (dispatchInput_work a) hvalid
  refine ⟨k + 1, rf, ?_, ?_, ?_, ?_⟩
  · have hl : (dispatchInput a).stacks 149 = a.stacks 149 :=
      dispatchInput_frame a 149 (by decide)
    rw [hl] at hk
    omega
  · exact eval_liftCommand_from_state FactorDispatch.command 149 154 id lowStack
      (callbackInitial a) Function.injective_id (Fin.castAdd_injective _ _) he
  · rw [show (dispatched a rf rows clauses marked mark factor).regs 5 =
        (FactorDispatch.finished (dispatchInput a) rf rows clauses marked mark factor).regs 5 from
      embedState_register id lowStack _ _ Function.injective_id 5]
    rw [FactorDispatch.finished_role_hash, h5]
  · rw [show (dispatched a rf rows clauses marked mark factor).regs 6 =
        (FactorDispatch.finished (dispatchInput a) rf rows clauses marked mark factor).regs 6 from
      embedState_register id lowStack _ _ Function.injective_id 6]
    rw [FactorDispatch.finished_role_marked, h6]

/-- The two conditionals are charged in their actual chosen branch. -/
theorem choose_hash {k : ℕ} {a b : FactorAssignmentProgram.Data}
    (h5 : a.regs 5 = true) (he : Eval hashFactor k a b) :
    Eval choose (k + 1) a b :=
  Eval.ite_true h5 he

theorem choose_marked {k : ℕ} {a b : FactorAssignmentProgram.Data}
    (h5 : a.regs 5 = false) (h6 : a.regs 6 = true)
    (he : Eval markedFactor k a b) : Eval choose (k + 2) a b := by
  simpa only [choose, Nat.add_assoc] using
    (Eval.ite_false h5 (Eval.ite_true h6 he) :
      Eval (.ite 5 hashFactor (.ite 6 markedFactor (.base .skip))) (k + 1 + 1) a b)

/-- Compose the actual clear, dispatcher, chosen branch and record return.
The branch frame is the one supplied by native table/arithmetic execution. -/
theorem callback_chosen_eval {n B d : ℕ}
    (a b : FactorAssignmentProgram.Data) (rf : Fin 8 → Bool) (rows clauses : List (List Bool))
    (marked : Bool) (mark factor kd kc : ℕ) (out : FactorAssignmentLoop.Raw n B d)
    (hrows : a.stacks 701 = Encoding.encodeList id rows)
    (hclauses : a.stacks 700 = Encoding.encodeList id clauses)
    (hcount : a.stacks 704 = List.replicate rows.length true)
    (hmark : a.stacks 705 = Encoding.encodeNat mark)
    (hclean : ∀ i ∈ callbackScratch, a.stacks (lowStack i) = [])
    (hd : Eval (liftLow FactorDispatch.command 149 154) kd (callbackInitial a)
      (dispatched a rf rows clauses marked mark factor))
    (hc : Eval choose kc (dispatched a rf rows clauses marked mark factor) b)
    (hb : b.stacks = Function.update
      (Function.update (dispatched a rf rows clauses marked mark factor).stacks 154 [])
      151 (Product.bytes out)) :
    Eval callback (clearCallbackCost a + (kd + (kc + (2 * (a.stacks 149).length + 6))))
      a (callbackFinished b) ∧
    (callbackFinished b).stacks =
      Function.update (Function.update a.stacks 149 []) 151 (Product.bytes out) ∧
    (callbackFinished b).regs 13 = false ∧
    (callbackFinished b).regs 14 = true ∧
    (callbackFinished b).regs 15 = false := by
  have hstart := callbackInitial_stacks a hclean
  have hw := dispatched_stacks a rf rows clauses marked mark factor hrows hclauses hcount hmark
  have h154 : a.stacks 154 = [] := hclean 154 (by decide)
  have hframe : b.stacks = Function.update a.stacks 151 (Product.bytes out) := by
    rw [hb, hw, hstart]
    funext i
    by_cases hi151 : i = 151 <;> by_cases hi154 : i = 154
    all_goals simp [hi151, hi154, h154]
  have h149 : b.stacks 149 = a.stacks 149 := by rw [hframe]; simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [callback, h149] using
      (clearCallback_eval a).seq (hd.seq (hc.seq (callbackFinish_eval b)))
  · funext i
    by_cases hi149 : i = 149 <;> by_cases hi151 : i = 151
    all_goals simp [callbackFinished, returned, cleared, hframe, hi149, hi151]
  all_goals simp [callbackFinished, returned]

/-- A neutral ID leaves the actual accumulated dictionary unchanged and
restores the same callback boundary, after its paid dispatch and return. -/
theorem callback_neutral_frame (a : FactorAssignmentProgram.Data) (rows clauses : List (List Bool))
    (marked : Bool) (mark factor : ℕ)
    (hrows : a.stacks 701 = Encoding.encodeList id rows)
    (hclauses : a.stacks 700 = Encoding.encodeList id clauses)
    (hcount : a.stacks 704 = List.replicate rows.length true)
    (hmark : a.stacks 705 = Encoding.encodeNat mark)
    (hflag : a.stacks 706 = [marked])
    (hfactor : a.stacks 149 = (Encoding.encodeNat factor).reverse)
    (hvalid : marked = true → mark < clauses.length)
    (hhash : ¬factor < rows.length)
    (hmarked : (marked && decide (factor = rows.length)) = false)
    (hclean : ∀ i ∈ callbackScratch, a.stacks (lowStack i) = []) :
    ∃ steps b, steps ≤ clearCallbackCost a + 9 * (a.stacks 149).length + 15 +
        LeafFactorDispatchProgram.budget rows clauses mark factor ∧
      Eval callback steps a b ∧ b.stacks = Function.update a.stacks 149 [] ∧
      b.regs 13 = false ∧ b.regs 14 = true ∧ b.regs 15 = false := by
  obtain ⟨steps, b, hs, he, hb, h13, h14, h15⟩ :=
    callback_neutral_eval a rows clauses marked mark factor hrows hclauses hcount hmark
      hflag hfactor hvalid hhash hmarked
  exact ⟨steps, b, hs, he, hb.trans
    (congrArg (fun ss : Fin 896 → List Bool => Function.update ss 149 [])
      (callbackInitial_stacks a hclean)), h13, h14, h15⟩

/-- Exact callback byte restoration supplies the state expected by the
record-fold theorem, while allowing the accumulator encoding to change. -/
theorem result_eq_state {n B d : ℕ} (base : Fin 896 → List Bool)
    (regs : Fin 40 → Bool) (seed out : FactorAssignmentLoop.Raw n B d)
    (tail payload : List Bool) (b : FactorAssignmentProgram.Data)
    (hb : b.stacks = Function.update
      (Function.update (FactorAssignmentLoop.state base regs seed tail payload).stacks 149 [])
      151 (Product.bytes out)) :
    b = FactorAssignmentLoop.state base b.regs out tail [] := by
  cases b with
  | mk rb sb =>
    apply congrArg (StructuredProgram.State.mk rb)
    funext i
    have hi := congrFun hb i
    by_cases h149 : i = 149 <;> by_cases h150 : i = 150 <;> by_cases h151 : i = 151
    all_goals simpa [FactorAssignmentLoop.state, Function.update_apply, h149, h150, h151] using hi

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback
