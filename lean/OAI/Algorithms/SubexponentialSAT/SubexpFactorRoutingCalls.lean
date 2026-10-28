import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRoutingControl
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Concrete subroutine calls for the assignment-driven factor router. -/

namespace SubexponentialSAT.SubexpFactorRoutingCalls

open BitProgram StructuredCalls SubexpScanPrimitives SubexpFactorRoutingControl
open Subexp.AssignmentAlphabetSemantics

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev unary (n : ℕ) := List.replicate n true

def cleared (d : Data) (src : Fin 48) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem clear_eval (d : Data) (src : Fin 48) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared d src) :=
  Subexp.TupleProgram.clear_eval src 0 1 d

theorem copy_eval (d : Data) (src dst : Fin 48)
    (hsd : src ≠ dst) (hs26 : src ≠ 26) (h26d : (26 : Fin 48) ≠ dst)
    (h26 : d.stacks 26 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (afterCopy d src dst 0 1) :=
  SubexpScanPrimitives.copy_eval d src dst 26 0 1 hsd hs26 h26d (by decide) h26

def taken (d : Data) (word rest : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,
    ArrayPrograms.countedTransferStacks 20 7 21 word rest d.stacks⟩

theorem takeWord_eval (d : Data) (word rest : List Bool)
    (hs : d.stacks 7 = word ++ rest) (hlen : (d.stacks 20).length = word.length) :
    Eval takeWord (4 * word.length + 3) d (taken d word rest) := by
  have ht := ArrayPrograms.countedTransferProgram_trace (20 : Fin 48) 7 21
    (0 : Fin 16) 1 (by decide) (by decide) (by decide) (by decide)
    word rest (d.stacks 20) d.regs d.stacks hs rfl hlen
  have hh := StackRoutines.halt_after_trace _ ht 4 rfl rfl
  exact .call _ (by simpa [SubexpFactorRoutingControl.takeWord, taken, ArrayPrograms.countedTransferResult,
    StructuredProgram.State.withPC, ArrayPrograms.countedTransferProgram, Nat.add_assoc] using hh)

def pulled (d : Data) (word rest : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update (Function.update d.stacks 7 rest) 10 word⟩

theorem pullWord_eval (d : Data) (word rest : List Bool)
    (hs : d.stacks 7 = word ++ rest) (hlen : (d.stacks 5).length = word.length)
    (h10 : d.stacks 10 = []) (h20 : d.stacks 20 = [])
    (h21 : d.stacks 21 = []) (h26 : d.stacks 26 = []) :
    Eval pullWord (14 * word.length + 11) d (pulled d word rest) := by
  let a := afterCopy d 5 20 0 1
  let b := taken a word rest
  have h1 := copy_eval d 5 20 (by decide) (by decide) (by decide) h26
  have h2 := takeWord_eval a word rest
    (by simpa [a, afterCopy, StackRoutines.copyStacks] using hs)
    (by simpa [a, afterCopy, StackRoutines.copyStacks, h20] using hlen)
  have h3 := SubexpScanPrimitives.transfer_eval b 21 10 0 1 (by decide) (by decide)
  have he : afterTransfer b 21 10 0 1 = pulled d word rest := by
    apply state_ext
    · simp [b, a, taken, afterCopy, afterTransfer, pulled, StackRoutines.readRegs_reset]
    · funext i
      by_cases h7i : i = 7 <;> by_cases h10i : i = 10 <;>
        by_cases h20i : i = 20 <;> by_cases h21i : i = 21 <;>
        simp [b, a, taken, afterCopy, afterTransfer, pulled,
          ArrayPrograms.countedTransferStacks, StackRoutines.copyStacks,
          StackRoutines.transferStacks,
          h7i, h10i, h20i, h21i, h10, h20, h21]
  rw [he] at h3
  have hcost : (b.stacks 21).length = word.length := by
    simp [b, taken, a, afterCopy, ArrayPrograms.countedTransferStacks,
      StackRoutines.copyStacks, h21]
  rw [hcost] at h3
  have hr := h1.seq (h2.seq h3)
  convert hr using 1
  all_goals simp only [pullWord, transfer, hlen]
  all_goals omega

theorem word_split {r Q : ℕ} (w : MulticolorTypes.Word r Q) (t : Fin Q) :
    ∃ (earlier : List (List Bool)) (rest : List Bool), earlier.length = t.val ∧
      (∀ row ∈ earlier, row.length = r) ∧
      Subexp.ReadPlan.encodeWord w = earlier.flatten ++ (oneHot (w t) ++ rest) := by
  let rows := List.ofFn (fun q : Fin Q => oneHot (w q))
  have ht : t.val < rows.length := by
    rw [show rows.length = Q by simp [rows]]
    exact t.isLt
  have he := List.take_append_drop t.val rows
  rw [List.drop_eq_getElem_cons ht] at he
  have hcell : rows[t.val] = oneHot (w t) := by simp [rows]
  rw [hcell] at he
  refine ⟨rows.take t.val, (rows.drop (t.val + 1)).flatten, ?_, ?_, ?_⟩
  · simp [List.length_take, rows]
  · intro row hr
    obtain ⟨q, hq⟩ := List.mem_ofFn.mp (List.mem_of_mem_take hr)
    rw [← hq]
    simp [oneHot]
  · change rows.flatten = _
    exact (congrArg List.flatten he).symm.trans
      (by simp [List.flatten_append, List.flatten_cons])

def colored (d : Data) (g : ℕ) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 11 (unary g)⟩

theorem readColor_eval {r Q : ℕ} (w : MulticolorTypes.Word r Q) (t : Fin Q)
    (d : Data) (hs : d.stacks 10 = Subexp.ReadPlan.encodeWord w)
    (ht : d.stacks 13 = unary t.val) (hr : d.stacks 4 = unary r)
    (hc : ∀ i ∈ ([11,14,15,16,17,18,19] : List (Fin 48)), d.stacks i = []) :
    ∃ n ≤ readColorBudget t.val r, Eval readColor n d (colored d (w t).val) := by
  let a := projectState registers5 colorPorts d
  obtain ⟨earlier, rest, hlen, hrows, hsplit⟩ := word_split w t
  have hclean : SubexpHeadColorProgram.Clean a := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simpa [a, projectState, colorPorts] using hc _ (by simp)
  obtain ⟨n, hn, he⟩ := SubexpHeadColorProgram.command_eval_oneHot a earlier (w t) rest
    (by simpa [a, projectState, colorPorts] using hs.trans hsplit)
    (by simpa [a, projectState, colorPorts, ht] using hlen.symm)
    (by simp [a, projectState, colorPorts, hr]) hrows hclean
  have hcall := eval_call_from_state SubexpHeadColorProgram.program registers5 colorPorts d
    registers5_injective colorPorts_injective (compiled_halt_trace he 0 3)
  have hout : embedState registers5 colorPorts d (SubexpHeadColorProgram.result a (w t).val) =
      colored d (w t).val := by
    apply embedState_eq _ _ registers5_injective colorPorts_injective
    · intro i
      fin_cases i <;> simp [a, projectState, SubexpHeadColorProgram.result,
        colored, registers5, readRegs]
    · intro i
      fin_cases i <;> simp [a, projectState, SubexpHeadColorProgram.result, colored, colorPorts]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, by simpa [registers5] using h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, by simpa [registers5] using h.symm⟩
      simp [colored, readRegs, h0, h1]
    · intro i hi
      have h11 : i ≠ 11 := fun h => hi ⟨3, by simpa [colorPorts] using h.symm⟩
      simp [colored, h11]
  rw [hout] at hcall
  refine ⟨n + 1, ?_, hcall⟩
  simpa only [hlen, readColorBudget] using Nat.add_le_add_right hn 1

def converted (d : Data) (dst : Fin 48) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 0 false) 1 false) 2 false,
    Function.update (Function.update d.stacks 24 []) dst (unary (CounterPrograms.value (d.stacks 24)))⟩

theorem convertIndex_eval (d : Data) (dst : Fin 48) (hd24 : dst ≠ 24) (hd25 : dst ≠ 25)
    (hd : d.stacks dst = []) (h25 : d.stacks 25 = []) :
    ∃ n ≤ CounterConversions.runtimeBound (d.stacks 24),
      Eval (convertIndex dst) n d (converted d dst) := by
  let a := CounterConversions.state (d.regs ∘ registers3) (d.stacks 24) []
  let b := CounterConversions.state CounterConversions.zeroRegs []
    (unary (CounterPrograms.value (d.stacks 24)))
  have ha : projectState registers3 (conversionPorts dst) d = a := by
    apply state_ext
    · rfl
    · funext i
      fin_cases i <;> simp [a, projectState, conversionPorts, CounterConversions.state, hd, h25]
  obtain ⟨n, hn, ht⟩ := CounterConversions.unary_runs (d.regs ∘ registers3) (d.stacks 24) []
  have ht' : Trace CounterConversions.unaryProgram n
      ((projectState registers3 (conversionPorts dst) d).withPC
        (some CounterConversions.unaryProgram.entry)) (b.withPC none) := by
    simpa only [ha, a, b, List.append_nil] using ht
  have he := eval_call_from_state CounterConversions.unaryProgram registers3 (conversionPorts dst) d
    registers3_injective (conversionPorts_injective dst hd24 hd25) ht'
  have hb : embedState registers3 (conversionPorts dst) d b = converted d dst := by
    apply embedState_eq _ _ registers3_injective (conversionPorts_injective dst hd24 hd25)
    · intro i
      fin_cases i <;> simp [b, CounterConversions.state, CounterConversions.zeroRegs,
        converted, registers3]
    · intro i
      fin_cases i <;> simp [b, CounterConversions.state, converted, conversionPorts,
        Ne.symm hd24, Ne.symm hd25, h25]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0, by simpa [registers3] using h.symm⟩
      have h1 : i ≠ 1 := fun h => hi ⟨1, by simpa [registers3] using h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨2, by simpa [registers3] using h.symm⟩
      simp [converted, h0, h1, h2]
    · intro i hi
      have h24 : i ≠ 24 := fun h => hi ⟨0, by simpa [conversionPorts] using h.symm⟩
      have hid : i ≠ dst := fun h => hi ⟨1, by simpa [conversionPorts] using h.symm⟩
      simp [converted, h24, hid]
  rw [hb] at he
  exact ⟨n, hn, he⟩

theorem compareColors_eval (d : Data) :
    ∃ n ≤ 9 * ((d.stacks 11).length + 1), ∃ regs : Fin 16 → Bool,
      ∃ left right : List Bool,
      regs 4 = decide (d.stacks 11 = d.stacks 22) ∧
      (∀ i : Fin 16, 5 ≤ i.val → regs i = d.regs i) ∧
      left.length ≤ (d.stacks 11).length ∧ right.length ≤ (d.stacks 22).length ∧
      Eval compareColors n d
        ⟨regs, Function.update (Function.update d.stacks 11 left) 22 right⟩ := by
  obtain ⟨c, ⟨n, hn, ht⟩, hpc, hout, hl, hr⟩ :=
    ExecClauseCost.bitEquality_runsIn_bounded (d.regs ∘ registers5) (d.stacks 11) (d.stacks 22)
  let a := projectState registers5 equalityPorts d
  let b : State 5 2 := ⟨c.regs, c.stacks⟩
  have hin : a.withPC (some ExecClauseCost.bitEqualityProgram.entry) =
      ExecClauseCost.bitEqualityStart (d.regs ∘ registers5) (d.stacks 11) (d.stacks 22) := by
    have hs : a.stacks = ExecClauseCost.bitStacks (d.stacks 11) (d.stacks 22) := by
      funext i
      fin_cases i <;> rfl
    change (⟨some 0, d.regs ∘ registers5, a.stacks⟩ : Cfg 5 2 10) = _
    rw [hs]
    rfl
  have hcfg : b.withPC none = c := by
    cases c
    simp_all [b, StructuredProgram.State.withPC]
  have ht' : Trace ExecClauseCost.bitEqualityProgram n
      (a.withPC (some ExecClauseCost.bitEqualityProgram.entry)) (b.withPC none) := by
    rw [hin, hcfg]
    exact ht
  have he := eval_call_from_state ExecClauseCost.bitEqualityProgram registers5 equalityPorts d
    registers5_injective equalityPorts_injective ht'
  let e := embedState registers5 equalityPorts d b
  have hs : e.stacks = Function.update (Function.update d.stacks 11 (c.stacks 0)) 22 (c.stacks 1) := by
    funext i
    by_cases h11 : i = 11
    · subst i
      simpa [e, equalityPorts] using
        embedState_stack registers5 equalityPorts d b equalityPorts_injective 0
    by_cases h22 : i = 22
    · subst i
      simpa [e, equalityPorts] using
        embedState_stack registers5 equalityPorts d b equalityPorts_injective 1
    · have hframe := embedState_stack_frame registers5 equalityPorts d b i (by
        rintro ⟨j, hj⟩
        fin_cases j <;> simp_all [equalityPorts])
      simpa [e, h11, h22] using hframe
  have hflag : e.regs 4 = decide (d.stacks 11 = d.stacks 22) := by
    change e.regs (registers5 4) = _
    rw [embedState_register _ _ _ _ registers5_injective]
    exact hout
  have hframe : ∀ i : Fin 16, 5 ≤ i.val → e.regs i = d.regs i := by
    intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    have := j.isLt
    omega
  have heq : e = ⟨e.regs,
      Function.update (Function.update d.stacks 11 (c.stacks 0)) 22 (c.stacks 1)⟩ := state_ext rfl hs
  change Eval compareColors n d e at he
  rw [heq] at he
  exact ⟨n, hn, e.regs, c.stacks 0, c.stacks 1, hflag, hframe, hl, hr, he⟩

def emitted (d : Data) : Data :=
  ⟨Function.update (Function.update d.regs 0 true) 1 false,
    Function.update (Function.update d.stacks 9 []) 23
      (Subexp.TupleProgram.prependRecord (d.stacks 9).reverse (d.stacks 23))⟩

theorem emit_eval (d : Data) :
    Eval emit (5 * (d.stacks 9).length + 7) d (emitted d) := by
  let a := Subexp.TupleProgram.pushedState 23 0 false d
  let b := Subexp.TupleProgram.escapedState emitPorts a
  let c := Subexp.TupleProgram.pushedState 23 0 true b
  have h1 := Subexp.TupleProgram.pushConst_eval (23 : Fin 48) (0 : Fin 16) false d
  have h2 := Subexp.TupleProgram.escape_eval_state emitPorts a
  have h3 := Subexp.TupleProgram.pushConst_eval (23 : Fin 48) (0 : Fin 16) true b
  have hc : c = emitted d := by
    apply state_ext
    · funext i
      by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;>
        simp [c, b, a, emitted, emitPorts, readRegs, h0, h1]
    · funext i
      by_cases h9 : i = 9 <;> by_cases h23 : i = 23 <;>
        simp [c, b, a, emitted, emitPorts, Subexp.TupleProgram.prependRecord,
          Subexp.TupleProgram.frame_eq_escaped, List.append_assoc, h9, h23]
  have he := h1.seq (h2.seq h3)
  change Eval emit _ d c at he
  rw [hc] at he
  convert he using 1
  all_goals simp [a, emitPorts]
  all_goals omega

theorem select_eval (d : Data) (keep : Bool) (hkeep : d.regs 4 = keep) :
    ∃ n ≤ 5 * (d.stacks 9).length + 8, ∃ e : Data,
      Eval (.ite 4 emit (clear 9)) n d e ∧
      e.stacks = Function.update (Function.update d.stacks 9 []) 23
        (if keep then Subexp.TupleProgram.prependRecord (d.stacks 9).reverse (d.stacks 23)
         else d.stacks 23) ∧
      (∀ i : Fin 16, 5 ≤ i.val → e.regs i = d.regs i) := by
  cases keep with
  | true =>
      refine ⟨5 * (d.stacks 9).length + 7 + 1, by omega, emitted d,
        .ite_true hkeep (emit_eval d), rfl, ?_⟩
      intro i hi
      have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
      have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
      simp [emitted, h0, h1]
  | false =>
      refine ⟨2 * (d.stacks 9).length + 3 + 1, by omega, cleared d 9,
        .ite_false hkeep (clear_eval d 9), ?_, ?_⟩
      · funext i
        by_cases h9 : i = 9 <;> by_cases h23 : i = 23 <;>
          simp [cleared, h9, h23]
      · intro i hi
        have h0 : i ≠ 0 := by intro h; subst i; norm_num at hi
        have h1 : i ≠ 1 := by intro h; subst i; norm_num at hi
        simp [cleared, readRegs, h0, h1]

end SubexponentialSAT.SubexpFactorRoutingCalls

end OAI.Algorithms
