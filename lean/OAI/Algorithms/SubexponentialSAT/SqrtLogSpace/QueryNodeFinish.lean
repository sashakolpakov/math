import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

/-! Actual node readout and loop continuation. The emitted coefficient stream
retains its order. Node temporaries are physically reclaimed before refreshing
the outer guard, and every completed node restores one fixed boundary bound. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

/-- The outer node loop refreshes its guard after all inner controllers. -/
def guardCursor : Code := .base (.atom (.peek 301 37 38))

def guarded (a : Data) : Data :=
  ⟨readRegs a.regs 37 38 (a.stacks 301).head?,a.stacks⟩

theorem guardCursor_eval (a : Data) : Eval guardCursor 1 a (guarded a) :=
  .base (.atom (.peek 301 37 38) a)

theorem guarded_test (a : Data) (nodes : List (List Bool))
    (hc : a.stacks 301=Encoding.encodeList id nodes) :
    (guarded a).regs 37 = !nodes.isEmpty ∧ (guarded a).regs 38=true := by
  cases nodes <;> simp [guarded,readRegs,hc,Encoding.encodeList]

def advanceIndex : Code := .seq (.base (.atom (.set 0 true))) (.base (.atom (.push 307 0)))

def advanced (a : Data) : Data :=
  ⟨Function.update a.regs 0 true,Function.update a.stacks 307 (true::a.stacks 307)⟩

theorem advanceIndex_eval (a : Data) : Eval advanceIndex 2 a (advanced a) := by
  have he := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 40) true) a)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push (307 : Fin 896) 0) _))
  simpa [advanceIndex,advanced,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using he

/-- Called after actual node readout and append. The retained node accumulator
and theta are reclaimed before the next node, then the index and guard advance. -/
def finishNode : Code := .seq (NodeReadoutSpace.clearMany [78,850])
  (.seq advanceIndex guardCursor)

def finished (a : Data) : Data :=
  guarded (advanced (NodeReadoutSpace.clearedMany [78,850] a))

def finishNodeCost (a : Data) : ℕ := 2*((a.stacks 78).length+(a.stacks 850).length)+9

theorem finishNode_eval (a : Data) : Eval finishNode (finishNodeCost a) a (finished a) := by
  have he := (NodeReadoutSpace.clearMany_eval [78,850] a).seq
    ((advanceIndex_eval _).seq (guardCursor_eval _))
  convert he using 1
  all_goals first
  | rfl
  | (simp [finishNodeCost,NodeReadoutSpace.clearCost,NodeReadoutSpace.cleared]; omega)

theorem finished_stacks (a : Data) : (finished a).stacks =
    Function.update (Function.update (Function.update a.stacks 78 []) 850 [])
      307 (true::a.stacks 307) := by
  funext i
  by_cases h307 : i=307
  · subst i
    simp [finished,guarded,advanced,NodeReadoutSpace.clearedMany_stack]
  by_cases h850 : i=850
  · subst i
    simp [finished,guarded,advanced,NodeReadoutSpace.clearedMany_stack]
  by_cases h78 : i=78
  · subst i
    simp [finished,guarded,advanced,NodeReadoutSpace.clearedMany_stack]
  simp [finished,guarded,advanced,NodeReadoutSpace.clearedMany_stack,h307,h850,h78]

theorem finished_index (a : Data) (index : ℕ) (hi : a.stacks 307=List.replicate index true) :
    (finished a).stacks 307=List.replicate (index+1) true := by
  simp [finished_stacks,hi,List.replicate_succ]

theorem finished_frame (a : Data) (i : Fin 896)
    (h78 : i≠78) (h850 : i≠850) (h307 : i≠307) :
    (finished a).stacks i=a.stacks i := by
  simp [finished_stacks,h78,h850,h307]

theorem finished_guard (a : Data) (nodes : List (List Bool))
    (hc : a.stacks 301=Encoding.encodeList id nodes) :
    (finished a).regs 37 = !nodes.isEmpty ∧ (finished a).regs 38=true := by
  apply guarded_test
  simpa [advanced,NodeReadoutSpace.clearedMany_stack] using hc

theorem finished_bound (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length ≤ B)
    (hx : (a.stacks 307).length+1 ≤ B) : ∀ i,((finished a).stacks i).length ≤ B := by
  intro i
  rw [finished_stacks]
  by_cases h307 : i=307
  · subst i
    simpa using hx
  by_cases h850 : i=850
  · subst i
    simp
  by_cases h78 : i=78
  · subst i
    simp
  simpa [Function.update_of_ne h307,Function.update_of_ne h850,Function.update_of_ne h78] using hb i

theorem finishNode_run_space (a : Data) (B : ℕ) (hb : ∀ i,(a.stacks i).length ≤ B)
    (hx : (a.stacks 307).length+1 ≤ B) :
    let p := compiled finishNode 850 863
    Trace p (finishNodeCost a+1) (a.withPC (some p.entry)) ((finished a).withPC none) ∧
      finishNodeCost a+1 ≤ 4*B+10 ∧ (∀ i,((finished a).stacks i).length ≤ B) ∧
      ∀ q z,q ≤ finishNodeCost a+1 → Trace p q (a.withPC (some p.entry)) z →
        ∀ i,(z.stacks i).length ≤ 900*B+10 := by
  dsimp only
  have ht : finishNodeCost a+1 ≤ 4*B+10 := by
    have := hb 78
    have := hb 850
    unfold finishNodeCost
    omega
  refine ⟨compiled_halt_trace (finishNode_eval a) 850 863,ht,finished_bound a B hb hx,?_⟩
  intro q z hq he i
  have hi : dataBits (a.withPC (some (compiled finishNode 850 863).entry)) ≤ 896*B :=
    StreamResources.dataBits_le_mul _ hb
  have hh := StructuredSpace.local_stack_bound (compiled finishNode 850 863)
    (steps:=4*B+10) hi q z (by omega) he i
  omega

def command : Code := .seq NodeAppendSpace.command finishNode

def program := compiled command 850 863

noncomputable def result (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool) : Data :=
  finished (NodeAppendSpace.result a rr modulus width degree dictionary zero
    marker taylor shape bits)

def touchedPorts : List (Fin 896) :=
  [5, 12, 39, 78, 307, 850, 862, 863] ++ NodeReadoutSpace.scratchPorts

theorem result_frame (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : NodeAppendSpace.MasterReady a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) (hi : i ∉ touchedPorts) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i =
      a.stacks i := by
  simp only [touchedPorts, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, not_or] at hi
  rw [result, finished_frame _ i hi.1.2.2.2.1 hi.1.2.2.2.2.2.1 hi.1.2.2.2.2.1]
  exact NodeAppendSpace.result_frame a rr _ _ _ _ _ _ _ _ _ hr i
    hi.1.1 hi.1.2.1 hi.1.2.2.1 hi.1.2.2.2.2.2.2.1 hi.1.2.2.2.2.2.2.2 hi.2

/-- The node cursor, marked collectors and high pair inputs survive exactly. -/
theorem result_high_frame (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : NodeAppendSpace.MasterReady a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) (hi : 128 ≤ i.val)
    (h307 : i ≠ 307) (h850 : i ≠ 850) (h862 : i ≠ 862) (h863 : i ≠ 863) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i =
      a.stacks i := by
  apply result_frame a rr _ _ _ _ _ _ _ _ _ hr i
  simp only [touchedPorts, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, not_or]
  refine ⟨⟨?_, ?_, ?_, ?_, h307, h850, h862, h863⟩, ?_⟩
  · intro h; have hv : i.val = 5 := congrArg Fin.val h; omega
  · intro h; have hv : i.val = 12 := congrArg Fin.val h; omega
  · intro h; have hv : i.val = 39 := congrArg Fin.val h; omega
  · intro h; have hv : i.val = 78 := congrArg Fin.val h; omega
  · intro hs
    have hl := NodeReadoutSpace.scratchPorts_low hs
    omega

theorem result_output (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : NodeAppendSpace.MasterReady a modulus width degree dictionary zero marker taylor shape) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks 863 =
      a.stacks 863 ++ bits := by
  rw [result, finished_frame _ 863 (by decide) (by decide) (by decide)]
  exact NodeAppendSpace.result_output a rr _ _ _ _ _ _ _ _ _ hr

theorem result_index (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : NodeAppendSpace.MasterReady a modulus width degree dictionary zero marker taylor shape)
    (index : ℕ) (hi : a.stacks 307 = List.replicate index true) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks 307 =
      List.replicate (index + 1) true := by
  apply finished_index
  exact (NodeAppendSpace.result_frame a rr _ _ _ _ _ _ _ _ _ hr 307
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi

theorem result_guard (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : NodeAppendSpace.MasterReady a modulus width degree dictionary zero marker taylor shape)
    (nodes : List (List Bool)) (hc : a.stacks 301 = Encoding.encodeList id nodes) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).regs 37 =
      !nodes.isEmpty ∧
    (result a rr modulus width degree dictionary zero marker taylor shape bits).regs 38 = true := by
  apply finished_guard
  exact (NodeAppendSpace.result_frame a rr _ _ _ _ _ _ _ _ _ hr 301
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc

theorem result_bound (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : NodeAppendSpace.MasterReady a modulus width degree dictionary zero marker taylor shape)
    (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hout : (a.stacks 863).length + bits.length ≤ B)
    (hx : (a.stacks 307).length + 1 ≤ B) :
    ∀ i, ((result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i).length
      ≤ B := by
  apply finished_bound _ B (NodeAppendSpace.result_bound a rr _ _ _ _ _ _ _ _ _ hr B ha hout)
  rw [NodeAppendSpace.result_frame a rr _ _ _ _ _ _ _ _ _ hr 307
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact hx

def budget (n wordWidth d u J incoming : ℕ) : ℕ :=
  NodeAppendSpace.budget n wordWidth d u J incoming + 4 * incoming + 10

/-- Actual scalar caches and a Good empty-support node array suffice for the
whole readout, ordered append, cleanup, index update and fresh guard. -/
theorem command_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (entries : List (Product.Entry n (baseWidth p t) d))
    (he : Good ∅ u J entries) (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (width degree marker taylor shape : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hu : marker.length = u) (hJ : taylor.length = J) (hs : shape.length = n)
    (a : Data) (incoming : ℕ) (ha : ∀ i, (a.stacks i).length ≤ incoming)
    (hr : NodeAppendSpace.MasterReady a M.bits width degree (Product.bytes entries)
      (RingProgram.flat zero) marker taylor shape)
    (hout : (a.stacks 863).length + J * (d * baseWidth p t) ≤ incoming)
    (hx : (a.stacks 307).length + 1 ≤ incoming) :
    let bits := MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J
    ∃ steps rr,
      steps + 1 ≤ budget n (baseWidth p t) d u J incoming ∧
      Eval command steps a
        (result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
          marker taylor shape bits) ∧
      bits.length = J * (d * baseWidth p t) ∧
      (∀ i, ((result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
        marker taylor shape bits).stacks i).length ≤ incoming) := by
  dsimp only
  obtain ⟨steps, rr, hb, first, hl⟩ := NodeAppendSpace.command_eval p t M cache entries he zero
    width degree marker taylor shape hd hw hu hJ hs a incoming ha hr
  have hout' : (a.stacks 863).length +
      (MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J).length ≤ incoming := by
    simpa only [hl] using hout
  have ha' := NodeAppendSpace.result_bound a rr _ _ _ _ _ _ _ _ _ hr incoming ha hout'
  have h78 := ha' 78
  have h850 := ha' 850
  refine ⟨_, rr, ?_, first.seq (finishNode_eval _), hl,
    result_bound a rr _ _ _ _ _ _ _ _ _ hr incoming ha hout' hx⟩
  unfold budget finishNodeCost
  omega

/-- All prefixes include the full incoming frame and every readout temporary.
The endpoint returns to incoming rather than iterating the transient bound. -/
theorem run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (entries : List (Product.Entry n (baseWidth p t) d))
    (he : Good ∅ u J entries) (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (width degree marker taylor shape : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hu : marker.length = u) (hJ : taylor.length = J) (hs : shape.length = n)
    (a : Data) (incoming : ℕ) (ha : ∀ i, (a.stacks i).length ≤ incoming)
    (hr : NodeAppendSpace.MasterReady a M.bits width degree (Product.bytes entries)
      (RingProgram.flat zero) marker taylor shape)
    (hout : (a.stacks 863).length + J * (d * baseWidth p t) ≤ incoming)
    (hx : (a.stacks 307).length + 1 ≤ incoming) :
    let bits := MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J
    ∃ steps rr,
      steps ≤ budget n (baseWidth p t) d u J incoming ∧
      Trace program steps (a.withPC (some program.entry))
        ((result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
          marker taylor shape bits).withPC none) ∧
      bits.length = J * (d * baseWidth p t) ∧
      (result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
        marker taylor shape bits).stacks 863 = a.stacks 863 ++ bits ∧
      (∀ i, ((result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
        marker taylor shape bits).stacks i).length ≤ incoming) ∧
      ∀ q z, q ≤ steps → Trace program q (a.withPC (some program.entry)) z →
        ∀ i, (z.stacks i).length ≤
          896 * incoming + budget n (baseWidth p t) d u J incoming := by
  dsimp only
  obtain ⟨steps, rr, hb, ht, hl, hf⟩ := command_eval p t M cache entries he zero
    width degree marker taylor shape hd hw hu hJ hs a incoming ha hr hout hx
  refine ⟨steps + 1, rr, hb, compiled_halt_trace ht 850 863, hl,
    result_output a rr _ _ _ _ _ _ _ _ _ hr, hf, ?_⟩
  intro q z hq hz i
  have hbits : dataBits (a.withPC (some program.entry)) ≤ 896 * incoming :=
    StreamResources.dataBits_le_mul _ ha
  exact StructuredSpace.local_stack_bound program hbits q z (hq.trans hb) hz i

theorem budget_polynomial (n wordWidth d u J incoming : ℕ) :
    budget n wordWidth d u J incoming ≤
      29 * incoming + 27 +
      (41 * (2 * incoming + 3) + 30000 * (n + wordWidth + d + u + J + 1) ^ 6 + 1) +
      6 * (incoming + J * (d * wordWidth)) + 9 + 4 * incoming + 10 :=
  Nat.add_le_add_right
    (Nat.add_le_add_right (NodeAppendSpace.budget_polynomial n wordWidth d u J incoming) _) _

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish
