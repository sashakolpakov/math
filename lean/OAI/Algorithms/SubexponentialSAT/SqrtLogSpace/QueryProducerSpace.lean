import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSpecializationProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

/-! Immediate Boolean specialization followed by the actual additive dictionary
normalizer. The input is a polynomial-size origin/singleton incidence stream;
no multivariate product is materialized before specialization. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram
open scoped BigOperators

/-- The source arithmetic uses its original twenty-eight ports. -/
def normalizePorts : Fin 28 → Fin 38 := Fin.castAdd 10

def scanPorts : Fin 10 → Fin 38 := Fin.natAdd 28

def scanRegisters : Fin 5 → Fin 8 := Fin.castAdd 3

theorem normalizePorts_injective : Function.Injective normalizePorts :=
  Fin.castAdd_injective _ _

theorem scanPorts_injective : Function.Injective scanPorts := by
  intro i j h
  exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

theorem scanRegisters_injective : Function.Injective scanRegisters :=
  Fin.castAdd_injective _ _

def state (regs : Fin 8 → Bool) (modulus width degree dict source : List Bool)
    (scan : MomentsProjectionProgram.Tape) : State 8 38 :=
  ⟨regs, fun i => Fin.addCases (m := 28) (n := 10) (motive := fun _ => List Bool)
    (Normalize.state regs modulus width degree dict source).stacks
    (MomentsProjectionProgram.tapes scan) i⟩

noncomputable def scanOverlay (regs : Fin 8 → Bool) (rr : Fin 5 → Bool) : Fin 8 → Bool :=
  Function.extend scanRegisters rr regs

theorem scanOverlay_same (regs : Fin 8 → Bool) :
    scanOverlay regs (regs ∘ scanRegisters) = regs := by
  funext i
  by_cases hi : ∃ j, scanRegisters j = i
  · obtain ⟨j, rfl⟩ := hi
    exact scanRegisters_injective.extend_apply _ _ _
  · exact Function.extend_apply' _ _ _ hi

theorem embed_scan (regs : Fin 8 → Bool) (rr : Fin 5 → Bool)
    (modulus width degree dict source : List Bool) (a b : MomentsProjectionProgram.Tape) :
    embedState scanRegisters scanPorts (state regs modulus width degree dict source a)
      (MomentsProjectionProgram.machine rr b) =
      state (scanOverlay regs rr) modulus width degree dict source b := by
  apply SubexpScanPrimitives.embedState_eq _ _ scanRegisters_injective scanPorts_injective
  · intro i
    exact scanRegisters_injective.extend_apply _ _ _
  · intro i
    simp [state, scanPorts, MomentsProjectionProgram.machine]
  · intro i hi
    exact Function.extend_apply' _ _ _ hi
  · intro i hi
    have hlt : i.val < 28 := by
      by_contra h
      let j : Fin 10 := ⟨i.val - 28, by omega⟩
      apply hi
      refine ⟨j, ?_⟩
      apply Fin.ext
      simp only [scanPorts, Fin.val_natAdd, j]
      omega
    let j : Fin 28 := ⟨i.val, hlt⟩
    have hj : normalizePorts j = i := Fin.ext rfl
    rw [← hj]
    simp [state, normalizePorts, Normalize.state, Normalize.extend, Dictionary.machine]

theorem embed_normalize (regs rr : Fin 8 → Bool)
    (modulus width degree dict source dict' source' : List Bool)
    (scan : MomentsProjectionProgram.Tape) :
    embedState id normalizePorts (state regs modulus width degree dict source scan)
      (Normalize.state rr modulus width degree dict' source') =
      state rr modulus width degree dict' source' scan := by
  apply SubexpScanPrimitives.embedState_eq _ _ Function.injective_id normalizePorts_injective
  · intro i
    rfl
  · intro i
    simp [state, normalizePorts]
  · intro i hi
    exact (hi ⟨i, rfl⟩).elim
  · intro i hi
    have hge : 28 ≤ i.val := by
      by_contra h
      apply hi
      exact ⟨⟨i.val, by omega⟩, Fin.ext rfl⟩
    let j : Fin 10 := ⟨i.val - 28, by omega⟩
    have hj : scanPorts j = i := by
      apply Fin.ext
      simp only [scanPorts, Fin.val_natAdd, j]
      omega
    rw [← hj]
    simp [state, scanPorts]

def scanCall : Cmd 8 38 :=
  .call (ProgramLinking.liftProgram HeadEvaluationProgram.Specialization.program
    scanRegisters scanPorts)

def handoff : Cmd 8 38 :=
  .seq (.call (StackRoutines.transferProgram 37 36 0 1))
    (.call (StackRoutines.transferProgram 36 27 0 1))

def normalizeCall : Cmd 8 38 :=
  .call (ProgramLinking.liftProgram Normalize.program id normalizePorts)

def command : Cmd 8 38 := .seq scanCall (.seq handoff normalizeCall)

def program := compiled command 28 15

/-- Both transfers are executed: the normalizer receives the original byte
order, while all handoff scratch is emptied. -/
theorem handoff_eval (regs : Fin 8 → Bool) (modulus width degree mask bits : List Bool) :
    Eval handoff (6 * bits.length + 6)
      (state regs modulus width degree [] [] {target := mask, framed := bits})
      (state (readRegs (readRegs regs 0 1 none) 0 1 none)
        modulus width degree [] bits {target := mask}) := by
  let a := state regs modulus width degree [] [] {target := mask, framed := bits}
  let b := SubexpScanPrimitives.afterTransfer a 37 36 0 1
  have h₁ := SubexpScanPrimitives.transfer_eval a 37 36 0 1 (by decide) (by decide)
  have h₂ := SubexpScanPrimitives.transfer_eval b 36 27 0 1 (by decide) (by decide)
  have hfinal : SubexpScanPrimitives.afterTransfer b 36 27 0 1 =
      state (readRegs (readRegs regs 0 1 none) 0 1 none)
        modulus width degree [] bits {target := mask} := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      fin_cases i <;> first | rfl |
        simp [a, b, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
          state, Fin.addCases, Normalize.state, Normalize.extend, Dictionary.machine,
          Dictionary.outputTape, Dictionary.tapes, MomentsProjectionProgram.tapes, Fin.snoc, Fin.coe_ofNat_eq_mod]
  have h := h₁.seq h₂
  rw [hfinal] at h
  unfold handoff
  convert h using 1
  have ha37 : (a.stacks 37).length = bits.length := by
    simp [a, state, MomentsProjectionProgram.tapes, Fin.addCases, Fin.coe_ofNat_eq_mod]
  have hb36 : (b.stacks 36).length = bits.length := by
    simp [b, a, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
      state, MomentsProjectionProgram.tapes, Fin.addCases, Fin.coe_ofNat_eq_mod]
  rw [ha37, hb36]
  omega

/-- Escape bits without the final delimiter, used only in the framing proof. -/
def escaped : List Bool → List Bool
  | [] => []
  | bit :: bits => true :: bit :: escaped bits

theorem escaped_append (a b : List Bool) : escaped (a ++ b) = escaped a ++ escaped b := by
  induction a with
  | nil => rfl
  | cons bit bits ih => simp [escaped, ih]

theorem escaped_frame (bits : List Bool) : escaped bits ++ [false] = Encoding.frame bits := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp [escaped, Encoding.frame, ih]

def frameData (regs : Fin 8 → Bool) (modulus width degree remaining output : List Bool) :
    State 8 38 := state regs modulus width degree [] [] {input := output, tmp2 := remaining}

def frameReady (regs : Fin 8 → Bool) (modulus width degree remaining output : List Bool) :
    State 8 38 := frameData (readRegs regs 0 1 remaining.head?)
      modulus width degree remaining output

def frameBody : StructuredProgram.Cmd 8 38 :=
  .seq (.atom (.pop 35 0 1)) (.seq (.atom (.push 28 0))
    (.seq (.atom (.set 0 true)) (.seq (.atom (.push 28 0)) (.atom (.peek 35 0 1)))))

def frameLoop : StructuredProgram.Cmd 8 38 := .while 1 frameBody

def framer : StructuredProgram.Cmd 8 38 :=
  .seq (.atom (.set 0 false)) (.seq (.atom (.push 28 0))
    (.seq (.atom (.peek 35 0 1)) frameLoop))

/-- The public producer takes separate forward raw dictionary and mask words;
the escaped prefix is constructed by actual stack instructions. -/
def prepare : Cmd 8 38 :=
  .seq (.call (StackRoutines.transferProgram 29 35 0 1)) (.base framer)

theorem frameBody_eval (regs : Fin 8 → Bool)
    (modulus width degree output : List Bool) (bit : Bool) (bits : List Bool) :
    ∃ rr, StructuredProgram.Eval frameBody 5
      (frameData regs modulus width degree (bit :: bits) output)
      (frameReady rr modulus width degree bits (true :: bit :: output)) := by
  let a := frameData regs modulus width degree (bit :: bits) output
  let b := (StructuredProgram.Atom.pop 35 0 1).eval a
  let c := (StructuredProgram.Atom.push 28 0).eval b
  let d := (StructuredProgram.Atom.set 0 true).eval c
  let e := (StructuredProgram.Atom.push 28 0).eval d
  have he := (StructuredProgram.Eval.atom (.pop 35 0 1) a).seq
    ((StructuredProgram.Eval.atom (.push 28 0) b).seq
    ((StructuredProgram.Eval.atom (.set 0 true) c).seq
    ((StructuredProgram.Eval.atom (.push 28 0) d).seq
      (StructuredProgram.Eval.atom (.peek 35 0 1) e))))
  refine ⟨e.regs, ?_⟩
  unfold frameBody
  convert he using 1
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext i
    fin_cases i <;> rfl

theorem frameLoop_eval (bits output : List Bool) (regs : Fin 8 → Bool)
    (modulus width degree : List Bool) :
    ∃ rr, StructuredProgram.Eval frameLoop (6 * bits.length + 1)
      (frameReady regs modulus width degree bits output)
      (frameData rr modulus width degree [] (escaped bits.reverse ++ output)) := by
  induction bits generalizing output regs with
  | nil =>
    refine ⟨readRegs regs 0 1 none, ?_⟩
    exact StructuredProgram.Eval.while_false (by simp [frameReady, frameData, state, readRegs])
  | cons bit bits ih =>
    obtain ⟨rb, hb⟩ := frameBody_eval (readRegs regs 0 1 (some bit))
      modulus width degree output bit bits
    obtain ⟨rr, hr⟩ := ih (true :: bit :: output) rb
    have he := StructuredProgram.Eval.while_true (body := frameBody)
      (by simp [frameReady, frameData, state, readRegs] :
        (frameReady regs modulus width degree (bit :: bits) output).regs 1 = true) hb hr
    refine ⟨rr, ?_⟩
    unfold frameLoop
    convert he using 1
    · simp only [List.length_cons]
      omega
    · simp [escaped_append, escaped, List.append_assoc]

theorem framer_eval (bits output : List Bool) (regs : Fin 8 → Bool)
    (modulus width degree : List Bool) :
    ∃ rr, StructuredProgram.Eval framer (6 * bits.length + 4)
      (frameData regs modulus width degree bits output)
      (frameData rr modulus width degree [] (Encoding.frame bits.reverse ++ output)) := by
  let a := frameData regs modulus width degree bits output
  let b := (StructuredProgram.Atom.set 0 false).eval a
  let c := (StructuredProgram.Atom.push 28 0).eval b
  have hp := StructuredProgram.Eval.atom (.peek 35 0 1) c
  have hc : (StructuredProgram.Atom.peek 35 0 1).eval c =
      frameReady c.regs modulus width degree bits (false :: output) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
  rw [hc] at hp
  obtain ⟨rr, hr⟩ := frameLoop_eval bits (false :: output) c.regs modulus width degree
  have he := (StructuredProgram.Eval.atom (.set 0 false) a).seq
    ((StructuredProgram.Eval.atom (.push 28 0) b).seq (hp.seq hr))
  refine ⟨rr, ?_⟩
  unfold framer
  convert he using 1
  · omega
  · rw [← escaped_frame]
    simp [frameData, List.append_assoc]

theorem prepare_eval (regs : Fin 8 → Bool) (modulus width degree mask raw : List Bool) :
    ∃ rr, Eval prepare (9 * mask.length + 7)
      (state regs modulus width degree [] [] {input := raw, target := mask})
      (state rr modulus width degree [] [] {input := Encoding.frame mask ++ raw}) := by
  let a := state regs modulus width degree [] [] {input := raw, target := mask}
  have ht := SubexpScanPrimitives.transfer_eval a 29 35 0 1 (by decide) (by decide)
  have hb : SubexpScanPrimitives.afterTransfer a 29 35 0 1 =
      frameData (readRegs regs 0 1 none) modulus width degree mask.reverse raw := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      fin_cases i <;> first | rfl |
        simp [SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, a,
          frameData, state, MomentsProjectionProgram.tapes, Fin.addCases, Fin.coe_ofNat_eq_mod]
  rw [hb] at ht
  obtain ⟨rr, hr⟩ := framer_eval mask.reverse raw (readRegs regs 0 1 none)
    modulus width degree
  refine ⟨rr, ?_⟩
  have he := ht.seq (Eval.base hr)
  unfold prepare
  convert he using 1
  · change 9 * mask.length + 7 = 3 * mask.length + 3 + (6 * mask.reverse.length + 4)
    simp only [List.length_reverse]
    omega
  · unfold frameData
    simp only [List.reverse_reverse]

def budget (n B d u J N L : ℕ) : ℕ :=
  200 * (L + 1) * (n + 2) + 1 + 6 * L + 6 +
    TruncatedRingProgram.normalizationBudget n B d u J N + 1

/-- Specialization retains only valid empty-support keys, allowing collisions
which the following actual normalizer adds in the coefficient ring. -/
theorem specialized_valid {n B d u J : ℕ} (U : Finset (Fin n))
    (source : List (Product.Entry n B d))
    (hsource : ∀ a ∈ source, Product.ValidKey Finset.univ u J a.1) :
    ∀ a ∈ HeadEvaluation.specializeEntries U source, Product.ValidKey ∅ u J a.1 := by
  intro a ha
  obtain ⟨b, hb, _, rfl⟩ := HeadEvaluation.mem_specializeEntries U source a ha
  exact ⟨(hsource b hb).1, by simp [Squarefree.Index.Valid], by simp⟩

theorem specialized_bytes_length {n B d : ℕ} (U : Finset (Fin n))
    (source : List (Product.Entry n B d)) :
    (Product.bytes (HeadEvaluation.specializeEntries U source)).length ≤
      (Product.bytes source).length := by
  induction source with
  | nil => rfl
  | cons a source ih =>
    by_cases h : a.1.vars ⊆ U <;>
      simp [HeadEvaluation.specializeEntries, h, Product.bytes, Normalize.bytes,
        Squarefree.Program.encodeDictionary, Squarefree.Program.rawEntries,
        Squarefree.encodeIndex] at * <;> omega

/-- A single finite program specializes raw records and normalizes equal keys.
Every stack at every prefix, including both copies and scalar caches, is charged. -/
theorem run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J N : ℕ} (U : Finset (Fin n))
    (source : List (Product.Entry n (baseWidth p t) d))
    (hsource : ∀ a ∈ source, Product.ValidKey Finset.univ u J a.1)
    (hN : source.length ≤ N) (regs : Fin 8 → Bool) (width degree : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    let result := Normalize.run p t M cache (HeadEvaluation.specializeEntries U source) []
    let start := state regs M.bits width degree [] []
      {input := Encoding.frame (Squarefree.encodeMask U) ++ Product.bytes source}
    ∃ steps rr, steps ≤ budget n (baseWidth p t) d u J N (Product.bytes source).length ∧
      Trace program steps (start.withPC (some program.entry))
        ((state rr M.bits width degree (Product.bytes result) []
          {target := (Squarefree.encodeMask U).reverse}).withPC none) ∧
      Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace program prefixSteps (start.withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ stackBits start.stacks +
          budget n (baseWidth p t) d u J N (Product.bytes source).length := by
  dsimp only
  let entries := source.map (fun a => (a.1, RingProgram.flat a.2))
  obtain ⟨scanSteps, hscanSteps, scanRegs, hscan, _⟩ :=
    HeadEvaluationProgram.Specialization.raw_dictionary_run_space U entries (regs ∘ scanRegisters)
  have hbytes : Squarefree.Program.rawEntries
      (entries.map (fun a => (Squarefree.encodeIndex a.1, a.2))) = Product.bytes source := by
    simp [entries, Product.bytes, Normalize.bytes, Squarefree.Program.encodeDictionary,
      List.map_map, Function.comp_def]
  have hselected : Squarefree.Program.rawEntries
      ((HeadEvaluation.specializeEntries U entries).map
        (fun a => (Squarefree.encodeIndex a.1, a.2))) =
      Product.bytes (HeadEvaluation.specializeEntries U source) := by
    rw [show entries = source.map (fun a => (a.1, RingProgram.flat a.2)) from rfl,
      HeadEvaluation.specializeEntries_map]
    simp [Product.bytes, Normalize.bytes, Squarefree.Program.encodeDictionary, List.map_map, Function.comp_def]
  rw [hbytes] at hscanSteps hscan
  rw [hselected] at hscan
  have hscanCall := eval_call_lifted HeadEvaluationProgram.Specialization.program
    scanRegisters scanPorts
    (state regs M.bits width degree [] []
      {input := Encoding.frame (Squarefree.encodeMask U) ++ Product.bytes source})
    scanRegisters_injective scanPorts_injective hscan
  rw [embed_scan, scanOverlay_same, embed_scan] at hscanCall
  let midRegs := scanOverlay regs scanRegs
  have hhand := handoff_eval midRegs M.bits width degree (Squarefree.encodeMask U).reverse
    (Product.bytes (HeadEvaluation.specializeEntries U source))
  let normRegs := readRegs (readRegs midRegs 0 1 none) 0 1 none
  obtain ⟨normSteps, rr, hnormSteps, hnorm, hgood, _⟩ :=
    TruncatedRingProgram.normalization_run_space p t M cache
      (HeadEvaluation.specializeEntries U source) [] (specialized_valid U source hsource)
      ((HeadEvaluation.specializeEntries_length U source).trans hN) Good.nil
      normRegs width degree hd hw
  have hnormCall := eval_call_lifted Normalize.program id normalizePorts
    (state normRegs M.bits width degree []
      (Product.bytes (HeadEvaluation.specializeEntries U source))
      {target := (Squarefree.encodeMask U).reverse})
    Function.injective_id normalizePorts_injective hnorm
  rw [embed_normalize, embed_normalize] at hnormCall
  have heval := hscanCall.seq (hhand.seq hnormCall)
  have hbound : scanSteps + (6 * (Product.bytes
      (HeadEvaluation.specializeEntries U source)).length + 6) + normSteps + 1 ≤
      budget n (baseWidth p t) d u J N (Product.bytes source).length := by
    have hlen := specialized_bytes_length U source
    unfold budget
    omega
  refine ⟨_, rr, hbound, ?_, hgood, ?_⟩
  · simpa [program, command, scanCall, normalizeCall, Nat.add_assoc] using
      compiled_halt_trace heval 28 15
  · intro prefixSteps intermediate hp ht i
    exact StructuredSpace.local_stack_bound program (steps :=
      budget n (baseWidth p t) d u J N (Product.bytes source).length)
      (by rfl) prefixSteps intermediate (hp.trans hbound) ht i

/-- The public producer includes the physical framing loop in its fixed code. -/
def preparedCommand : Cmd 8 38 := .seq prepare (.call program)

def preparedProgram := compiled preparedCommand 28 15

def preparedBudget (n B d u J N L : ℕ) : ℕ := 9 * n + 8 + budget n B d u J N L

/-- A fixed exponent covers framing, scanning, handoff and normalization. -/
theorem preparedBudget_polynomial (n B d u J N L : ℕ) :
    preparedBudget n B d u J N L ≤
      3100000 * (n + B + d + u + J + N + L + 1) ^ 10 := by
  let a := n + B + d + u + J + N + L + 1
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hn : n ≤ a := by dsimp [a]; omega
  have hL : L ≤ a := by dsimp [a]; omega
  have hsum : n + B + d + u + J + N + 1 ≤ a := by dsimp [a]; omega
  have hnorm := (TruncatedRingProgram.normalizationBudget_le_local n B d u J N).trans
    (TruncatedRingProgram.localBudget_le n B d u J N)
  have hnorm' : TruncatedRingProgram.normalizationBudget n B d u J N ≤
      3000000 * a ^ 10 := hnorm.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsum 10))
  have hscan : 200 * (L + 1) * (n + 2) ≤ 200 * (a + 1) * (a + 2) := by gcongr
  have h0 : 1 ≤ a ^ 10 := Nat.one_le_pow 10 a ha
  have h1 : a ≤ a ^ 10 := by simpa using pow_le_pow_right' ha (show 1 ≤ 10 by decide)
  have h2 : a ^ 2 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  change preparedBudget n B d u J N L ≤ 3100000 * a ^ 10
  unfold preparedBudget budget
  have hexpand : 200 * (a + 1) * (a + 2) = 200 * a ^ 2 + 600 * a + 400 := by ring
  rw [hexpand] at hscan
  omega

/-- No serialized correction prefix is assumed: its bytes are produced on this
same run from the separate ambient mask, and all framing steps are charged. -/
theorem prepared_run_space (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J N : ℕ} (U : Finset (Fin n))
    (source : List (Product.Entry n (baseWidth p t) d))
    (hsource : ∀ a ∈ source, Product.ValidKey Finset.univ u J a.1)
    (hN : source.length ≤ N) (regs : Fin 8 → Bool) (width degree : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t) :
    let result := Normalize.run p t M cache (HeadEvaluation.specializeEntries U source) []
    let start := state regs M.bits width degree [] []
      {input := Product.bytes source, target := Squarefree.encodeMask U}
    ∃ steps rr, steps ≤ preparedBudget n (baseWidth p t) d u J N (Product.bytes source).length ∧
      Trace preparedProgram steps (start.withPC (some preparedProgram.entry))
        ((state rr M.bits width degree (Product.bytes result) []
          {target := (Squarefree.encodeMask U).reverse}).withPC none) ∧
      Good ∅ u J result ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace preparedProgram prefixSteps (start.withPC (some preparedProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ stackBits start.stacks +
          preparedBudget n (baseWidth p t) d u J N (Product.bytes source).length := by
  dsimp only
  obtain ⟨readyRegs, hprepare⟩ := prepare_eval regs M.bits width degree
    (Squarefree.encodeMask U) (Product.bytes source)
  obtain ⟨steps, rr, hsteps, hrun, hgood, _⟩ := run_space p t M cache U source
    hsource hN readyRegs width degree hd hw
  have he := hprepare.seq (Eval.call program hrun)
  have hbound : 9 * (Squarefree.encodeMask U).length + 7 + steps + 1 ≤
      preparedBudget n (baseWidth p t) d u J N (Product.bytes source).length := by
    simp only [Squarefree.encodeMask_length]
    unfold preparedBudget
    omega
  refine ⟨_, rr, hbound, ?_, hgood, ?_⟩
  · exact compiled_halt_trace he 28 15
  · intro prefixSteps intermediate hp ht i
    exact StructuredSpace.local_stack_bound preparedProgram
      (steps := preparedBudget n (baseWidth p t) d u J N (Product.bytes source).length)
      (by rfl) prefixSteps intermediate (hp.trans hbound) ht i

noncomputable section

variable {R : Type*} [CommRing R]

/-- The physically filtered record stream evaluates at the current Boolean
correction assignment. Erasing supports alone would not imply this identity. -/
theorem specialized_raw_denote {n B d : ℕ} (U : Finset (Fin n))
    (f : RingProgram.Code (Word B) d → R) (source : List (Product.Entry n B d)) :
    rawDenote f (HeadEvaluation.specializeEntries U source) =
      Moments.jetScalar (V := Fin n) (Moments.jetEval
        (fun v => if v ∈ U then (1 : R) else 0)
        (by intro v; split <;> simp) (rawDenote f source)) := by
  unfold rawDenote Dictionary.denoteTable
  rw [← HeadEvaluation.specializeEntries_map]
  exact HeadEvaluation.specializeEntries_denote U _

/-- The normalized machine output represents immediate Boolean specialization
in the bounded two-index ring, with no multivariate intermediate retained. -/
theorem normalized_specialization_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (u J : ℕ) (U : Finset (Fin n))
    (source : List (Product.Entry n (baseWidth p t) d)) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    TruncatedRingProgram.rawValue u J f
      (Normalize.run p t M cache (HeadEvaluation.specializeEntries U source) []) =
      Dense.ofPolynomial u J (Moments.jetEval
        (fun v => if v ∈ U then (1 : R) else 0)
        (by intro v; split <;> simp) (rawDenote f source)) := by
  dsimp only
  rw [TruncatedRingProgram.normalize_dense p t M cache scalar basis u J _ []
    (by simp [Squarefree.Sparse.keys])]
  have hnil : TruncatedRingProgram.rawValue (n := n) u J
      (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) [] = 0 := by
    simp [TruncatedRingProgram.rawValue, rawDenote, Dictionary.denoteTable,
      Squarefree.Sparse.denote, Squarefree.Sparse.decode]
  rw [hnil, add_zero, TruncatedRingProgram.rawValue, specialized_raw_denote,
    TruncatedRingProgram.jetProjection_jetScalar]


end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace
