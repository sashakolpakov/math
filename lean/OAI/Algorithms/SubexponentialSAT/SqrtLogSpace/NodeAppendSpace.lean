import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

abbrev Data := State 40 896
abbrev Code := Cmd 40 896

def transfer (src dst : Fin 896) : Code := .call (StackRoutines.transferProgram src dst 0 1)

def transferred (src dst : Fin 896) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.transferStacks src dst a.stacks⟩

theorem transfer_eval (src dst : Fin 896) (h : src ≠ dst) (a : Data) :
    Eval (transfer src dst) (3 * (a.stacks src).length + 3) a (transferred src dst a) :=
  .call _ (ListRegisterProgram.transfer_run src dst 0 1 h (by decide) a.regs a.stacks)

def append : Code := .seq (transfer 863 89) (.seq (transfer 862 89) (transfer 89 863))

def appendResult (a : Data) : Data :=
  transferred 89 863 (transferred 862 89 (transferred 863 89 a))

def appendCost (a : Data) : ℕ := 6 * ((a.stacks 863).length + (a.stacks 862).length) + 9

theorem append_eval (a : Data) (hs : a.stacks 89 = []) :
    Eval append (appendCost a) a (appendResult a) := by
  have h1 := transfer_eval 863 89 (by decide) a
  have h2 := transfer_eval 862 89 (by decide) (transferred 863 89 a)
  have h3 := transfer_eval 89 863 (by decide) (transferred 862 89 (transferred 863 89 a))
  convert h1.seq (h2.seq h3) using 1
  · rfl
  · simp [appendCost, transferred, StackRoutines.transferStacks, hs]
    omega
  · rfl

theorem appendResult_stacks (a : Data) (hs : a.stacks 89 = []) :
    (appendResult a).stacks = Function.update (Function.update
      (Function.update a.stacks 863 (a.stacks 863 ++ a.stacks 862)) 862 []) 89 [] := by
  funext i
  by_cases h863 : i = 863
  · subst i
    simp [appendResult, transferred, StackRoutines.transferStacks, hs]
  by_cases h862 : i = 862
  · subst i
    simp [appendResult, transferred, StackRoutines.transferStacks, hs]
  by_cases h89 : i = 89
  · subst i
    simp [appendResult, transferred, StackRoutines.transferStacks, hs]
  simp [appendResult, transferred, StackRoutines.transferStacks, h863, h862, h89]

def appendProgram := compiled append 862 863

theorem append_run_space (a : Data) (hs : a.stacks 89 = []) :
    Trace appendProgram (appendCost a + 1)
      (a.withPC (some appendProgram.entry)) ((appendResult a).withPC none) ∧
    ∀ steps b, steps ≤ appendCost a + 1 →
      Trace appendProgram steps (a.withPC (some appendProgram.entry)) b →
      ∀ i, (b.stacks i).length ≤ stackBits a.stacks + appendCost a + 1 := by
  refine ⟨compiled_halt_trace (append_eval a hs) 862 863, ?_⟩
  intro steps b hb ht i
  have hbits : dataBits (a.withPC (some appendProgram.entry)) ≤ stackBits a.stacks := by
    change stackBits a.stacks ≤ stackBits a.stacks
    exact le_rfl
  have h : (b.stacks i).length ≤ stackBits a.stacks + (appendCost a + 1) :=
    StructuredSpace.local_stack_bound appendProgram hbits steps b hb ht i
  omega

def copy (src dst : Fin 896) : Code := .call (StackRoutines.copyProgram src dst 89 0 1)

def copied (src dst : Fin 896) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks src dst a.stacks⟩

theorem copy_eval (src dst : Fin 896) (a : Data)
    (hsd : src ≠ dst) (hst : src ≠ 89) (htd : (89 : Fin 896) ≠ dst)
    (ht : a.stacks 89 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied src dst a) :=
  .call _ (ListRegisterProgram.copy_run src dst 89 0 1 hsd hst htd (by decide) a.regs a.stacks ht)

def prepare : Code := .seq (NodeReadoutSpace.clearMany [89,5,12,39])
  (.seq (copy 194 5) (.seq (copy 202 12) (copy 204 39)))

def prepared (a : Data) : Data := copied 204 39 (copied 202 12
  (copied 194 5 (NodeReadoutSpace.clearedMany [89,5,12,39] a)))

def prepareCost (a : Data) : ℕ := NodeReadoutSpace.clearCost [89,5,12,39] a +
  7 * (a.stacks 194).length + 5 + 7 * (a.stacks 202).length + 5 +
  7 * (a.stacks 204).length + 5

theorem prepare_eval (a : Data) : Eval prepare (prepareCost a) a (prepared a) := by
  let b := NodeReadoutSpace.clearedMany [89,5,12,39] a
  have hc := NodeReadoutSpace.clearMany_eval [89,5,12,39] a
  have h1 := copy_eval 194 5 b (by decide) (by decide) (by decide)
    (by simp [b, NodeReadoutSpace.clearedMany_stack])
  have h2 := copy_eval 202 12 (copied 194 5 b) (by decide) (by decide) (by decide)
    (by simp [copied, StackRoutines.copyStacks, b, NodeReadoutSpace.clearedMany_stack])
  have h3 := copy_eval 204 39 (copied 202 12 (copied 194 5 b)) (by decide) (by decide) (by decide)
    (by simp [copied, StackRoutines.copyStacks, b, NodeReadoutSpace.clearedMany_stack])
  convert hc.seq (h1.seq (h2.seq h3)) using 1
  · rfl
  · simp [prepareCost, copied, StackRoutines.copyStacks, b,
      NodeReadoutSpace.clearedMany_stack]
    omega
  · rfl

theorem prepared_stacks (a : Data) (i : Fin 896) :
    (prepared a).stacks i = if i = 5 then a.stacks 194 else if i = 12 then a.stacks 202
      else if i = 39 then a.stacks 204 else if i = 89 then [] else a.stacks i := by
  by_cases h5 : i = 5
  · subst i; simp [prepared, copied, StackRoutines.copyStacks, NodeReadoutSpace.clearedMany_stack]
  by_cases h12 : i = 12
  · subst i; simp [prepared, copied, StackRoutines.copyStacks, NodeReadoutSpace.clearedMany_stack]
  by_cases h39 : i = 39
  · subst i; simp [prepared, copied, StackRoutines.copyStacks, NodeReadoutSpace.clearedMany_stack]
  by_cases h89 : i = 89
  · subst i; simp [prepared, copied, StackRoutines.copyStacks, NodeReadoutSpace.clearedMany_stack]
  simp [prepared, copied, StackRoutines.copyStacks, NodeReadoutSpace.clearedMany_stack,
    h5, h12, h39, h89]

theorem prepareCost_le (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B) :
    prepareCost a ≤ 29 * B + 27 := by
  have hc := NodeReadoutSpace.clearCost_le [89,5,12,39] a B ha
  have h194 := ha 194
  have h202 := ha 202
  have h204 := ha 204
  simp only [List.length_cons, List.length_nil] at hc
  unfold prepareCost
  omega

theorem prepared_bound (a : Data) (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((prepared a).stacks i).length ≤ B := by
  intro i
  rw [prepared_stacks]
  split_ifs <;> first | exact ha _ | exact Nat.zero_le _

structure MasterReady (a : Data) (modulus width degree dictionary zero marker taylor shape : List Bool) : Prop where
  modulus : a.stacks 194 = modulus
  width : a.stacks 202 = width
  degree : a.stacks 204 = degree
  dictionary : a.stacks 850 = dictionary
  zero : a.stacks 280 = zero
  marker : a.stacks 212 = marker
  taylor : a.stacks 243 = taylor
  shape : a.stacks 128 = shape

theorem prepared_ready (a : Data)
    (modulus width degree dictionary zero marker taylor shape : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape) :
    NodeReadoutSpace.Ready (prepared a) modulus width degree dictionary zero marker taylor shape := by
  constructor
  · simpa [prepared_stacks] using hr.modulus
  · simpa [prepared_stacks] using hr.width
  · simpa [prepared_stacks] using hr.degree
  · simpa [prepared_stacks] using hr.dictionary
  · simpa [prepared_stacks] using hr.zero
  · simpa [prepared_stacks] using hr.marker
  · simpa [prepared_stacks] using hr.taylor
  · simpa [prepared_stacks] using hr.shape



theorem appendResult_bound (a : Data) (B : ℕ) (hs : a.stacks 89 = [])
    (ha : ∀ i, (a.stacks i).length ≤ B)
    (hout : (a.stacks 863).length + (a.stacks 862).length ≤ B) :
    ∀ i, ((appendResult a).stacks i).length ≤ B := by
  intro i
  rw [appendResult_stacks a hs]
  by_cases h89 : i = 89
  · subst i; simp
  by_cases h862 : i = 862
  · subst i; simp
  by_cases h863 : i = 863
  · subst i; simpa using hout
  simpa [Function.update_of_ne h89, Function.update_of_ne h862,
    Function.update_of_ne h863] using ha i

/-- Actual cache staging, original native readout, and order-preserving append. -/
def command : Code := .seq prepare (.seq NodeReadoutSpace.command append)

def program := compiled command 850 863

noncomputable def result (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool) : Data :=
  appendResult (NodeReadoutSpace.result (prepared a) rr modulus width degree dictionary zero
    marker taylor shape bits)

def budget (n B d u J incoming : ℕ) : ℕ :=
  29 * incoming + 27 + NodeReadoutSpace.budget n B d u J incoming +
    6 * (incoming + J * (d * B)) + 9

theorem readout_scratch (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape) :
    (NodeReadoutSpace.result (prepared a) rr modulus width degree dictionary zero
      marker taylor shape bits).stacks 89 = [] :=
  NodeReadoutSpace.result_scratch _ rr _ _ _ _ _ _ _ _ _
    (prepared_ready a _ _ _ _ _ _ _ _ hr) 89 (by decide)

theorem readout_stream (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape) :
    (NodeReadoutSpace.result (prepared a) rr modulus width degree dictionary zero
      marker taylor shape bits).stacks 863 = a.stacks 863 := by
  rw [NodeReadoutSpace.result_frame _ rr _ _ _ _ _ _ _ _ _
    (prepared_ready a _ _ _ _ _ _ _ _ hr) 863 (by decide) (by decide)]
  simp [prepared_stacks]

theorem result_output (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks 863 =
      a.stacks 863 ++ bits := by
  unfold result
  rw [appendResult_stacks _ (readout_scratch a rr _ _ _ _ _ _ _ _ _ hr)]
  simp only [Function.update_of_ne (show (863 : Fin 896) ≠ 89 from by decide),
    Function.update_of_ne (show (863 : Fin 896) ≠ 862 from by decide), Function.update_self]
  rw [readout_stream a rr _ _ _ _ _ _ _ _ _ hr, NodeReadoutSpace.result_output]

theorem result_frame (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) (h5 : i ≠ 5) (h12 : i ≠ 12) (h39 : i ≠ 39)
    (h862 : i ≠ 862) (h863 : i ≠ 863) (hs : i ∉ NodeReadoutSpace.scratchPorts) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i =
      a.stacks i := by
  have h89 : i ≠ 89 := by
    intro hi
    subst i
    exact hs (by decide)
  unfold result
  rw [appendResult_stacks _ (readout_scratch a rr _ _ _ _ _ _ _ _ _ hr)]
  simp only [Function.update_of_ne h89, Function.update_of_ne h862, Function.update_of_ne h863]
  rw [NodeReadoutSpace.result_frame _ rr _ _ _ _ _ _ _ _ _
    (prepared_ready a _ _ _ _ _ _ _ _ hr) i h862 hs]
  simp only [prepared_stacks, h5, h12, h39, h89, ite_false]

theorem result_empty (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape)
    (i : Fin 896) (hi : i = 862 ∨ i ∈ NodeReadoutSpace.scratchPorts) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i = [] := by
  unfold result
  rw [appendResult_stacks _ (readout_scratch a rr _ _ _ _ _ _ _ _ _ hr)]
  by_cases h89 : i = 89
  · subst i; simp
  by_cases h862 : i = 862
  · subst i; simp
  have hs := hi.resolve_left h862
  have h863 : i ≠ 863 := by
    have hl := NodeReadoutSpace.scratchPorts_low hs
    intro he
    subst i
    change 88 ≤ 863 ∧ 863 < 128 at hl
    omega
  simp only [Function.update_of_ne h89, Function.update_of_ne h862, Function.update_of_ne h863]
  exact NodeReadoutSpace.result_scratch _ rr _ _ _ _ _ _ _ _ _
    (prepared_ready a _ _ _ _ _ _ _ _ hr) i hs

theorem result_bound (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (hr : MasterReady a modulus width degree dictionary zero marker taylor shape)
    (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B)
    (hout : (a.stacks 863).length + bits.length ≤ B) :
    ∀ i, ((result a rr modulus width degree dictionary zero marker taylor shape bits).stacks i).length ≤ B := by
  apply appendResult_bound _ B (readout_scratch a rr _ _ _ _ _ _ _ _ _ hr)
  · exact NodeReadoutSpace.result_bound _ rr _ _ _ _ _ _ _ _ _
      (prepared_ready a _ _ _ _ _ _ _ _ hr) B (prepared_bound a B ha) (by omega)
  · rw [readout_stream a rr _ _ _ _ _ _ _ _ _ hr, NodeReadoutSpace.result_output]
    exact hout


/-- This fixed command includes the actual cache copies, native readout and all
three transfers. No staging or concatenation service is assumed. -/
theorem command_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (entries : List (Product.Entry n (baseWidth p t) d))
    (he : Good ∅ u J entries) (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (width degree marker taylor shape : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hu : marker.length = u) (hJ : taylor.length = J) (hs : shape.length = n)
    (a : Data) (incoming : ℕ) (ha : ∀ i, (a.stacks i).length ≤ incoming)
    (hr : MasterReady a M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
      marker taylor shape) :
    let bits := MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J
    ∃ steps rr,
      steps + 1 ≤ budget n (baseWidth p t) d u J incoming ∧
      Eval command steps a
        (result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
          marker taylor shape bits) ∧ bits.length = J * (d * baseWidth p t) := by
  dsimp only
  obtain ⟨steps, rr, hb, ht, hl⟩ := NodeReadoutSpace.command_eval p t M cache entries he zero
    width degree marker taylor shape hd hw hu hJ hs (prepared a) incoming
    (prepared_bound a incoming ha) (prepared_ready a _ _ _ _ _ _ _ _ hr)
  have heval := (prepare_eval a).seq (ht.seq (append_eval _
    (readout_scratch a rr _ _ _ _ _ _ _ _ _ hr)))
  refine ⟨_, rr, ?_, heval, hl⟩
  have hp := prepareCost_le a incoming ha
  have hslen := ha 863
  simp only [appendCost, readout_stream a rr _ _ _ _ _ _ _ _ _ hr,
    NodeReadoutSpace.result_output, hl]
  unfold budget
  omega

/-- The exact accumulated stream and all source prefixes belong to the same
concrete run. The bound includes all 896 incoming words and append scratch. -/
theorem run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (entries : List (Product.Entry n (baseWidth p t) d))
    (he : Good ∅ u J entries) (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (width degree marker taylor shape : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hu : marker.length = u) (hJ : taylor.length = J) (hs : shape.length = n)
    (a : Data) (incoming : ℕ) (ha : ∀ i, (a.stacks i).length ≤ incoming)
    (hr : MasterReady a M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
      marker taylor shape) :
    let bits := MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J
    ∃ steps rr,
      steps ≤ budget n (baseWidth p t) d u J incoming ∧
      Trace program steps (a.withPC (some program.entry))
        ((result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
          marker taylor shape bits).withPC none) ∧
      bits.length = J * (d * baseWidth p t) ∧
      (result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
        marker taylor shape bits).stacks 863 = a.stacks 863 ++ bits ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          896 * incoming + budget n (baseWidth p t) d u J incoming := by
  dsimp only
  obtain ⟨steps, rr, hb, ht, hl⟩ := command_eval p t M cache entries he zero
    width degree marker taylor shape hd hw hu hJ hs a incoming ha hr
  refine ⟨steps + 1, rr, hb, compiled_halt_trace ht 850 863, hl,
    result_output a rr _ _ _ _ _ _ _ _ _ hr, ?_⟩
  have hbits : dataBits (a.withPC (some program.entry)) ≤ 896 * incoming := by
    change (∑ i : Fin 896, (a.stacks i).length) ≤ _
    calc
      _ ≤ ∑ _ : Fin 896, incoming := Finset.sum_le_sum (fun i _ => ha i)
      _ = _ := by simp
  intro prefixSteps intermediate hp htrace i
  exact StructuredSpace.local_stack_bound program hbits prefixSteps intermediate
    (hp.trans hb) htrace i

theorem budget_polynomial (n B d u J incoming : ℕ) :
    budget n B d u J incoming ≤ 29 * incoming + 27 +
      (41 * (2 * incoming + 3) + 30000 * (n + B + d + u + J + 1) ^ 6 + 1) +
      6 * (incoming + J * (d * B)) + 9 := by
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_left (NodeReadoutSpace.budget_polynomial n B d u J incoming) _) _) _


theorem prepared_register_frame (a : Data) (i : Fin 40) (hi : 8 ≤ i.val) :
    (prepared a).regs i = a.regs i := by
  have h0 : i ≠ 0 := fun h => by subst i; simp at hi
  have h1 : i ≠ 1 := fun h => by subst i; simp at hi
  simp only [prepared, copied, StackRoutines.readRegs_frame _ 0 1 i none h0 h1]
  exact NodeReadoutSpace.clearedMany_register _ a i h0 h1

theorem result_register_frame (a : Data) (rr : Fin 8 → Bool)
    (modulus width degree dictionary zero marker taylor shape bits : List Bool)
    (i : Fin 40) (hi : 8 ≤ i.val) :
    (result a rr modulus width degree dictionary zero marker taylor shape bits).regs i =
      a.regs i := by
  have h0 : i ≠ 0 := fun h => by subst i; simp at hi
  have h1 : i ≠ 1 := fun h => by subst i; simp at hi
  simp only [result, appendResult, transferred,
    StackRoutines.readRegs_frame _ 0 1 i none h0 h1]
  rw [NodeReadoutSpace.result_register_frame _ rr _ _ _ _ _ _ _ _ _ i hi]
  exact prepared_register_frame a i hi

/-- Final paid handoff from the complete interpolation stream to the actual CRT
jet input. Two transfers retain the byte order. -/
def handoff : Code := .seq (NodeReadoutSpace.clearOne 265)
  (.seq (transfer 863 89) (transfer 89 265))

def handoffResult (a : Data) : Data :=
  transferred 89 265 (transferred 863 89 (NodeReadoutSpace.cleared 265 a))

def handoffCost (a : Data) : ℕ :=
  2 * (a.stacks 265).length + 6 * (a.stacks 863).length + 9

theorem handoff_eval (a : Data) (hs : a.stacks 89 = []) :
    Eval handoff (handoffCost a) a (handoffResult a) := by
  have hc := NodeReadoutSpace.clearOne_eval 265 a
  have h1 := transfer_eval 863 89 (by decide) (NodeReadoutSpace.cleared 265 a)
  have h2 := transfer_eval 89 265 (by decide)
    (transferred 863 89 (NodeReadoutSpace.cleared 265 a))
  convert hc.seq (h1.seq h2) using 1
  · rfl
  · simp [handoffCost, transferred, StackRoutines.transferStacks,
      NodeReadoutSpace.cleared, hs]
    omega
  · rfl

theorem handoffResult_stacks (a : Data) (hs : a.stacks 89 = []) :
    (handoffResult a).stacks = Function.update (Function.update
      (Function.update a.stacks 265 (a.stacks 863)) 863 []) 89 [] := by
  funext i
  by_cases h265 : i = 265
  · subst i
    simp [handoffResult, transferred, StackRoutines.transferStacks, NodeReadoutSpace.cleared, hs]
  by_cases h863 : i = 863
  · subst i
    simp [handoffResult, transferred, StackRoutines.transferStacks, NodeReadoutSpace.cleared, hs]
  by_cases h89 : i = 89
  · subst i
    simp [handoffResult, transferred, StackRoutines.transferStacks, NodeReadoutSpace.cleared, hs]
  simp [handoffResult, transferred, StackRoutines.transferStacks, NodeReadoutSpace.cleared,
    h265, h863, h89]

def handoffProgram := compiled handoff 863 265

theorem handoff_run_space (a : Data) (hs : a.stacks 89 = [])
    (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B) :
    Trace handoffProgram (handoffCost a + 1)
      (a.withPC (some handoffProgram.entry)) ((handoffResult a).withPC none) ∧
    handoffCost a + 1 ≤ 8 * B + 10 ∧
    ∀ steps b, steps ≤ handoffCost a + 1 →
      Trace handoffProgram steps (a.withPC (some handoffProgram.entry)) b →
      ∀ i, (b.stacks i).length ≤ 904 * B + 10 := by
  have h265 := ha 265
  have h863 := ha 863
  have hc : handoffCost a + 1 ≤ 8 * B + 10 := by unfold handoffCost; omega
  refine ⟨compiled_halt_trace (handoff_eval a hs) 863 265, hc, ?_⟩
  have hbits : dataBits (a.withPC (some handoffProgram.entry)) ≤ 896 * B := by
    change (∑ i : Fin 896, (a.stacks i).length) ≤ _
    calc
      _ ≤ ∑ _ : Fin 896, B := Finset.sum_le_sum (fun i _ => ha i)
      _ = _ := by simp
  intro steps b hb ht i
  have h : (b.stacks i).length ≤ 896 * B + (8 * B + 10) :=
    StructuredSpace.local_stack_bound handoffProgram hbits steps b (hb.trans hc) ht i
  omega

theorem handoffResult_bound (a : Data) (hs : a.stacks 89 = [])
    (B : ℕ) (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((handoffResult a).stacks i).length ≤ B := by
  intro i
  rw [handoffResult_stacks a hs]
  by_cases h89 : i = 89
  · subst i; simp
  by_cases h863 : i = 863
  · subst i; simp
  by_cases h265 : i = 265
  · subst i; simpa using ha 863
  simpa [Function.update_of_ne h89, Function.update_of_ne h863,
    Function.update_of_ne h265] using ha i

theorem handoffResult_register_frame (a : Data) (i : Fin 40) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    (handoffResult a).regs i = a.regs i := by
  simp only [handoffResult, transferred, NodeReadoutSpace.cleared,
    StackRoutines.readRegs_frame _ 0 1 i none h0 h1]

noncomputable section
variable {R : Type*} [CommRing R]

/-- The appended bytes are the actual increasing-order coefficient codes. The
readout is additive and is used only after the completed node-array sum. -/
theorem output_codes_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (entries : List (Product.Entry n (baseWidth p t) d))
    (he : Good ∅ u J entries) (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (hz : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis zero = 0)
    (a : Data) (rr : Fin 8 → Bool) (width degree marker taylor shape : List Bool)
    (hr : MasterReady a M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
      marker taylor shape) :
    let codes := MomentsReadoutProgram.outputCodes p t M cache entries u zero 0 J
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    (result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
      marker taylor shape (MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J)).stacks 863 =
        a.stacks 863 ++ (codes.map RingProgram.flat).flatten ∧
      Truncated.ofPolynomial J (PolynomialAlgorithm.denote (codes.map f)) =
        Dense.readout (rawValue u J f entries) := by
  dsimp only
  exact ⟨result_output a rr _ _ _ _ _ _ _ _ _ hr,
    TruncatedRingProgram.readout_codes_dense p t M cache scalar basis u J entries zero he.nodup hz⟩

end

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace
