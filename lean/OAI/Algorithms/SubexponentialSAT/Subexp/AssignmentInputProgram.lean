import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.OneHotAlphabetProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentAlphabetSemantics
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentRecordViews
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentSeedRange
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputCall
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInputState
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentInitProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreBounds

namespace OAI.Algorithms

/-!
# Physical input construction for sequential type assignment

All parameters are unary stack data. The fixed program constructs the one-hot
word alphabet, reads its actual first word, derives its packed view, and builds
the exact seed range and dimensions expected by `AssignmentInitProgram`.
-/

namespace SubexponentialSAT.Subexp.AssignmentInputProgram

open BitProgram StructuredCalls SubexpSetupStorage AssignmentInputCall

def seedCount (delta D E : ℕ) : ℕ := E + (delta + 1) * D

def context (r Q delta D E : ℕ) (pairs : List Bool) : AssignmentInitProgram.Context where
  defaultWord := (AssignmentAlphabetSemantics.wordBytes r Q).headD []
  packedAlphabet := (AssignmentAlphabetSemantics.wordBytes r Q).flatten
  alphabetRecords := ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes r Q)
  width := unary (Q * r)
  depth := unary (2 * (delta + 1))
  rawPairs := pairs
  seedRecords := AssignmentSeedRange.seedRecords (seedCount delta D E)
  seedCount := seedCount delta D E

def outputState (r Q delta D E : ℕ) (pairs : List Bool) : Data :=
  AssignmentInitProgram.inputState (context r Q delta D E pairs) (fun _ => false)

def colorAlphabet : Code := AssignmentInputCall.call OneHotAlphabetProgram.program
  (by decide) (by decide) [(1, 12)] 6 7

def wordAlphabet : Code := AssignmentInputCall.call TupleProgram.generateProgram
  (by decide) (by decide) [(7, 13), (2, 20)] 0 30

def firstWord : Code := AssignmentInputCall.call AssignmentRecordViews.firstProgram
  (by decide) (by decide) [(30, 12)] 2 0

def packedAlphabet : Code := AssignmentInputCall.call AssignmentRecordViews.flattenProgram
  (by decide) (by decide) [(30, 12)] 2 9

def wordWidth : Code := AssignmentInputCall.call BlockCopyProgram.program
  (by decide) (by decide) [(1, 12), (2, 15)] 1 10

def deltaPlusOne : Code := .seq (copyCmd 3 6 31) (TupleProgram.pushConst 6 0 true)

def depth : Code := copyMany 31 [(6, 34), (6, 34)]

def seedProduct : Code := AssignmentInputCall.call BlockCopyProgram.program
  (by decide) (by decide) [(4, 12), (6, 15)] 1 47

def seedSize : Code := .seq seedProduct (copyCmd 5 47 31)

def seedRange : Code := AssignmentInputCall.call AssignmentSeedRange.program
  (by decide) (by decide) [(47, 12)] 5 46

def cleanup : Code := .seq (clearMany [1, 2, 3, 4, 5, 6, 7]) (resetMany (List.finRange 16))

def command : Code :=
  .seq colorAlphabet (.seq wordAlphabet (.seq firstWord (.seq packedAlphabet
    (.seq wordWidth (.seq deltaPlusOne (.seq depth (.seq seedSize (.seq seedRange cleanup))))))))

abbrev program : Program 16 48 (size command + 1) := compiled command 1 30

/-- A physical stage changes one public stack and restores the private bank.
The witness is an actual measured execution of its finite instruction table. -/
def Writes (c : Code) (a : Data) (dst : Fin 48) (bits : List Bool) (charge : ℕ) : Prop :=
  ∃ ticks b, Eval c ticks a b ∧ b.stacks = Function.update a.stacks dst bits ∧ Clean b ∧
    ∀ B, Within a B → bits.length ≤ B → 1 ≤ B → ticks ≤ charge + 400 * (B + 1)

theorem colorAlphabet_eval (a : Data) (n : ℕ) (hc : Clean a)
    (h1 : a.stacks 1 = unary n) :
    Writes colorAlphabet a 7 (ProgramEncoding.encodeRecords (OneHotAlphabetProgram.rows 0 n))
      (60 * (n + 1) ^ 2 + 1) := by
  let pre := project (register (r := 5) (by decide)) (stack (s := 7) (by decide))
    (prepareState 31 work [(1, 12)] a)
  have hp : pre = OneHotAlphabetProgram.inputState pre.regs n := by
    apply congrArg (StructuredProgram.State.mk pre.regs)
    funext i
    have h := prepare_one_local (r := 5) (s := 7) (by decide) (by decide) a hc 1 0 i
    change pre.stacks i = _
    change pre.stacks i = _ at h
    rw [h]
    fin_cases i <;> simp [ h1]
  obtain ⟨ticks, htime, ht⟩ := OneHotAlphabetProgram.program_runsIn pre.regs n
  rw [← hp] at ht
  obtain ⟨b, he, hs, hb⟩ := call_eval OneHotAlphabetProgram.program
    (by decide) (by decide) [(1, 12)] 6 7 a (OneHotAlphabetProgram.outputState n)
    (by decide) (by decide) (by simp [mem_work]) (by simp) hc ht
  refine ⟨_, b, he, hs, hb, ?_⟩
  intro B ha hout _
  have ho : Within (OneHotAlphabetProgram.outputState n) B := by
    intro j; fin_cases j <;> simp [OneHotAlphabetProgram.outputState, hout]
  have h := callCost_le (r := 5) (s := 7) (by decide) (by decide)
    [(1, 12)] 6 7 a _ ticks B (by decide) ha ho
  exact h.trans (Nat.add_le_add_right htime _)

theorem wordAlphabet_eval (a : Data) (r Q : ℕ) (hc : Clean a)
    (h7 : a.stacks 7 = ProgramEncoding.encodeRecords (OneHotAlphabetProgram.rows 0 r))
    (h2 : a.stacks 2 = unary Q) :
    Writes wordAlphabet a 30 (ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes r Q))
      (TupleProgram.powerCost (OneHotAlphabetProgram.rows 0 r) Q [[]] + 9) := by
  let pre := project (register (r := 10) (by decide)) (stack (s := 9) (by decide))
    (prepareState 31 work [(7, 13), (2, 20)] a)
  have hs (i : Fin 9) : pre.stacks i =
      if i = 8 then unary Q else if i = 1 then
        ProgramEncoding.encodeRecords (OneHotAlphabetProgram.rows 0 r) else [] := by
    have h := prepare_two_local (r := 10) (s := 9)
      (by decide) (by decide) a hc 7 2 1 8 (by decide) (by decide) i
    change pre.stacks i = _ at h
    simpa only [h7, h2] using h
  have hp : TupleProgram.outerInvariant (OneHotAlphabetProgram.rows 0 r) (unary Q)
      (pre.regs 9) pre := by
    simp [TupleProgram.outerInvariant, hs]
  obtain ⟨out, hout, ticks, htime, ht⟩ := TupleProgram.generateProgram_runsIn
    (OneHotAlphabetProgram.rows 0 r) (unary Q) (pre.regs 9) pre hp
    (by simp [hs]) (by simp [hs]) (by simp [hs])
  obtain ⟨b, he, hb, hclean⟩ := call_eval TupleProgram.generateProgram
    (by decide) (by decide) [(7, 13), (2, 20)] 0 30 a out
    (by decide) (by decide) (by simp [mem_work]) (by simp) hc ht
  refine ⟨_, b, he, ?_, hclean, ?_⟩
  · rw [hb, hout.2.1]
    simp only [List.length_replicate, AssignmentAlphabetSemantics.wordBytes]
  · intro B ha hresult hB
    rcases hout with ⟨⟨h1, h3, h4, h6, h7', h8, h9⟩, h0, h2', h5⟩
    have halphabet : (ProgramEncoding.encodeRecords (OneHotAlphabetProgram.rows 0 r)).length ≤ B := by
      simpa only [← h7] using ha 7
    have ho : Within out B := by
      intro j
      fin_cases j <;> simp_all [AssignmentAlphabetSemantics.wordBytes]
    have h := callCost_le (r := 10) (s := 9) (by decide) (by decide)
      [(7, 13), (2, 20)] 0 30 a out ticks B (by decide) ha ho
    simp only [List.length_replicate] at htime
    exact h.trans (Nat.add_le_add_right htime _)

theorem firstWord_eval (a : Data) (bits : List Bool) (rows : List (List Bool))
    (hc : Clean a) (h30 : a.stacks 30 = ProgramEncoding.encodeRecords (bits :: rows)) :
    Writes firstWord a 0 bits (9 * bits.length + 10) := by
  let pre := project (register (r := 3) (by decide)) (stack (s := 3) (by decide))
    (prepareState 31 work [(30, 12)] a)
  have hp : pre = AssignmentRecordViews.data (pre.regs 0) (pre.regs 1) (pre.regs 2)
      (ProgramEncoding.encodeRecords (bits :: rows)) [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i
      have h := prepare_one_local (r := 3) (s := 3) (by decide) (by decide) a hc 30 0 i
      change pre.stacks i = _
      change pre.stacks i = _ at h
      rw [h]
      fin_cases i <;> simp [ h30]
  have ht := AssignmentRecordViews.first_trace (pre.regs 0) (pre.regs 1) (pre.regs 2) bits rows
  rw [← hp] at ht
  obtain ⟨b, he, hs, hb⟩ := call_eval AssignmentRecordViews.firstProgram
    (by decide) (by decide) [(30, 12)] 2 0 a
    (AssignmentRecordViews.data false false false (ProgramEncoding.encodeRecords rows) [] bits)
    (by decide) (by decide) (by simp [mem_work]) (by simp) hc ht
  refine ⟨_, b, he, hs, hb, ?_⟩
  intro B ha hresult _
  have htail : (ProgramEncoding.encodeRecords rows).length ≤ B := by
    have hh := ha 30
    rw [h30] at hh
    change (Encoding.encodeList id rows).length ≤ B
    change (Encoding.encodeList id (bits :: rows)).length ≤ B at hh
    rw [Encoding.length_encodeList_cons] at hh
    omega
  have ho : Within (AssignmentRecordViews.data false false false
      (ProgramEncoding.encodeRecords rows) [] bits) B := by
    intro j; fin_cases j <;> simp [ htail, hresult]
  exact callCost_le (r := 3) (s := 3) (by decide) (by decide)
    [(30, 12)] 2 0 a _ _ B (by decide) ha ho

theorem packedAlphabet_eval (a : Data) (rows : List (List Bool)) (hc : Clean a)
    (h30 : a.stacks 30 = ProgramEncoding.encodeRecords rows) :
    Writes packedAlphabet a 9 rows.flatten
      (9 * (rows.map List.length).sum + 6 * rows.length + 7) := by
  let pre := project (register (r := 3) (by decide)) (stack (s := 3) (by decide))
    (prepareState 31 work [(30, 12)] a)
  have hp : pre = AssignmentRecordViews.data (pre.regs 0) (pre.regs 1) (pre.regs 2)
      (ProgramEncoding.encodeRecords rows ++ []) [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i
      have h := prepare_one_local (r := 3) (s := 3) (by decide) (by decide) a hc 30 0 i
      change pre.stacks i = _
      change pre.stacks i = _ at h
      rw [h]
      fin_cases i <;> simp [ h30]
  have ht := AssignmentRecordViews.flatten_trace (pre.regs 0) (pre.regs 1) (pre.regs 2) rows [] []
  rw [← hp] at ht
  obtain ⟨b, he, hs, hb⟩ := call_eval AssignmentRecordViews.flattenProgram
    (by decide) (by decide) [(30, 12)] 2 9 a
    (AssignmentRecordViews.data false false false [] [] (rows.flatten ++ []))
    (by decide) (by decide) (by simp [mem_work]) (by simp) hc ht
  refine ⟨_, b, he, by simpa using hs, hb, ?_⟩
  intro B ha hresult _
  simp only [List.length_flatten] at hresult
  have ho : Within (AssignmentRecordViews.data false false false [] [] (rows.flatten ++ [])) B := by
    intro j; fin_cases j <;> simp [ hresult]
  exact callCost_le (r := 3) (s := 3) (by decide) (by decide)
    [(30, 12)] 2 9 a _ _ B (by decide) ha ho

theorem copies_unary (n m : ℕ) : BlockCopyProgram.copies n (unary m) = unary (n * m) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [BlockCopyProgram.copies_succ, ih]
      simp [unary, Nat.add_mul, Nat.add_comm]

theorem repeat_eval (a : Data) (src count dst : Fin 48) (m n : ℕ)
    (hc : Clean a) (hsrc : a.stacks src = unary m) (hcount : a.stacks count = unary n)
    (hd : dst ∉ work) (htmp : dst ≠ 31)
    (hports : ∀ x ∈ [(src, 12), (count, 15)],
      x.1 ≠ x.2 ∧ x.1 ≠ 31 ∧ (31 : Fin 48) ≠ x.2)
    (hcount12 : count ≠ 12) :
    Writes (AssignmentInputCall.call BlockCopyProgram.program (by decide) (by decide)
      [(src, 12), (count, 15)] 1 dst) a dst (unary (n * m))
      (n * (7 * m + 7) + 3) := by
  let pre := project (register (r := 3) (by decide)) (stack (s := 4) (by decide))
    (prepareState 31 work [(src, 12), (count, 15)] a)
  have hp : pre = BlockCopyProgram.initialState n (unary m) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      have h := prepare_regs [(src, 12), (count, 15)] a (register (by decide) i)
        (by have := i.isLt; simp only [register, Fin.val_castLE]; omega)
      fin_cases i <;> exact h
    · funext i
      have h := prepare_two_local (r := 3) (s := 4) (by decide) (by decide)
        a hc src count 0 3 (by decide) hcount12 i
      change pre.stacks i = _
      change pre.stacks i = _ at h
      rw [h]
      fin_cases i <;> simp [ hsrc, hcount]
  have ht := BlockCopyProgram.program_trace n (unary m) []
  rw [← hp] at ht
  obtain ⟨b, he, hs, hb⟩ := call_eval BlockCopyProgram.program
    (by decide) (by decide) [(src, 12), (count, 15)] 1 dst a
    (BlockCopyProgram.data false false (unary m) (BlockCopyProgram.copies n (unary m) ++ []) [])
    hd htmp (by simp [mem_work]) hports hc ht
  refine ⟨_, b, he, by simpa [BlockCopyProgram.data, copies_unary] using hs, hb, ?_⟩
  intro B ha hresult _
  simp only [List.length_replicate] at hresult
  have hm : m ≤ B := by simpa [hsrc] using ha src
  have ho : Within (BlockCopyProgram.data false false (unary m)
      (BlockCopyProgram.copies n (unary m) ++ []) []) B := by
    intro j; fin_cases j <;> simp [BlockCopyProgram.data, copies_unary, hm, hresult]
  simpa only [List.length_replicate] using callCost_le (r := 3) (s := 4)
    (by decide) (by decide) [(src, 12), (count, 15)] 1 dst a _ _ B (by simp) ha ho

theorem seedRange_eval (a : Data) (n : ℕ) (hc : Clean a)
    (h47 : a.stacks 47 = unary n) :
    Writes seedRange a 46 (AssignmentSeedRange.seedRecords n) (AssignmentSeedRange.budget n + 1) := by
  let pre := project (register (r := 5) (by decide)) (stack (s := 6) (by decide))
    (prepareState 31 work [(47, 12)] a)
  have hp : pre = AssignmentSeedRange.inputState pre.regs n := by
    apply congrArg (StructuredProgram.State.mk pre.regs)
    funext i
    have h := prepare_one_local (r := 5) (s := 6) (by decide) (by decide) a hc 47 0 i
    change pre.stacks i = _
    change pre.stacks i = _ at h
    rw [h]
    fin_cases i <;> simp [ h47]
  obtain ⟨ticks, htime, ht⟩ := AssignmentSeedRange.program_runsIn pre.regs n
  rw [← hp] at ht
  obtain ⟨b, he, hs, hb⟩ := call_eval AssignmentSeedRange.program
    (by decide) (by decide) [(47, 12)] 5 46 a (AssignmentSeedRange.outputState n)
    (by decide) (by decide) (by simp [mem_work]) (by simp) hc ht
  refine ⟨_, b, he, hs, hb, ?_⟩
  intro B ha hresult _
  have ho : Within (AssignmentSeedRange.outputState n) B := by
    intro j; fin_cases j <;> simp [AssignmentSeedRange.outputState, AssignmentSeedRange.state, hresult]
  have h := callCost_le (r := 5) (s := 6) (by decide) (by decide)
    [(47, 12)] 5 46 a _ ticks B (by decide) ha ho
  exact h.trans (Nat.add_le_add_right htime _)

theorem clean_of_update (a b : Data) (dst : Fin 48) (bits : List Bool)
    (hc : Clean a) (hd : dst ∉ work) (htmp : dst ≠ 31)
    (hs : b.stacks = Function.update a.stacks dst bits) : Clean b := by
  constructor
  · intro j hj
    have hn : j ≠ dst := by intro h; exact hd (h ▸ hj)
    simp [hs, hn, hc.1 j hj]
  · simp [hs, Ne.symm htmp, hc.2]

theorem within_of_update (a b : Data) (dst : Fin 48) (bits : List Bool) (B : ℕ)
    (ha : Within a B) (hb : bits.length ≤ B)
    (hs : b.stacks = Function.update a.stacks dst bits) : Within b B := by
  intro j
  by_cases hj : j = dst
  · subst j; simpa only [hs, Function.update_same] using hb
  · simpa [hs, Function.update_apply, hj] using ha j

theorem deltaPlusOne_eval (a : Data) (delta : ℕ) (hc : Clean a)
    (h3 : a.stacks 3 = unary delta) (h6 : a.stacks 6 = []) :
    Writes deltaPlusOne a 6 (unary (delta + 1)) (7 * delta + 7) := by
  let b := copyState 3 6 a
  let c := TupleProgram.pushedState 6 0 true b
  have h1 := copy_eval 3 6 31 a (by decide) (by decide) (by decide) hc.2
  have h2 := TupleProgram.pushConst_eval 6 0 true b
  have hs : c.stacks = Function.update a.stacks 6 (unary (delta + 1)) := by
    funext j
    by_cases hj : j = 6
    · subst j
      simp [c, b, copyState_stack, h3, h6, unary, List.replicate_succ]
    · simp [c, b, copyState_stack, hj]
  refine ⟨_, c, h1.seq h2, hs, clean_of_update a c 6 _ hc (by decide) (by decide) hs, ?_⟩
  intro B _ _ _
  simp only [h3, List.length_replicate]
  omega

theorem depth_eval (a : Data) (n : ℕ) (hc : Clean a)
    (h6 : a.stacks 6 = unary n) (h34 : a.stacks 34 = []) :
    Writes depth a 34 (unary (2 * n)) (14 * n + 10) := by
  let b := copyManyState [(6, 34), (6, 34)] a
  have h := copyMany_eval 31 [(6, 34), (6, 34)] a (by simp) hc.2
  have hs : b.stacks = Function.update a.stacks 34 (unary (2 * n)) := by
    funext j
    by_cases hj : j = 34
    · subst j
      simp [b, copyManyState, copyState_stack, h6, h34, unary,
 two_mul]
    · simp [b, copyManyState, copyState_stack, hj]
  refine ⟨_, b, h, hs, clean_of_update a b 34 _ hc (by decide) (by decide) hs, ?_⟩
  intro B _ _ _
  simp [copyManyCost, copyState_stack, h6]
  omega

theorem seedSize_eval (a : Data) (delta D E : ℕ) (hc : Clean a)
    (h4 : a.stacks 4 = unary D) (h6 : a.stacks 6 = unary (delta + 1))
    (h5 : a.stacks 5 = unary E) :
    Writes seedSize a 47 (unary (seedCount delta D E))
      ((delta + 1) * (7 * D + 7) + 3 + (7 * E + 5)) := by
  obtain ⟨ticks, b, hb, hs, hc', htime⟩ := repeat_eval a 4 6 47 D (delta + 1) hc h4 h6
    (by decide) (by decide) (by simp) (by decide)
  have hcopy := copy_eval 5 47 31 b (by decide) (by decide) (by decide) hc'.2
  let c := copyState 5 47 b
  have hout : c.stacks = Function.update a.stacks 47 (unary (seedCount delta D E)) := by
    funext j
    by_cases hj : j = 47
    · subst j
      simp [c, copyState_stack, hs, h5, seedCount, unary]
    · simp [c, copyState_stack, hs, hj]
  refine ⟨_, c, hb.seq hcopy, hout,
    clean_of_update a c 47 _ hc (by decide) (by decide) hout, ?_⟩
  intro B ha hresult hB
  have hproduct : (unary ((delta + 1) * D)).length ≤ B := by
    simp only [List.length_replicate, seedCount] at hresult ⊢
    omega
  have ht := htime B ha hproduct hB
  simp only [hs, Function.update_of_ne (show (5 : Fin 48) ≠ 47 by decide), h5,
    List.length_replicate]
  omega

theorem input_clean (regs : Fin 16 → Bool) (r Q delta D E : ℕ) (pairs : List Bool) :
    Clean (inputState regs r Q delta D E pairs) := by
  constructor
  · intro j hj
    rw [mem_work] at hj
    have h1 : j ≠ 1 := by intro h; subst j; change 12 ≤ 1 ∧ 1 < 22 at hj; omega
    have h2 : j ≠ 2 := by intro h; subst j; change 12 ≤ 2 ∧ 2 < 22 at hj; omega
    have h3 : j ≠ 3 := by intro h; subst j; change 12 ≤ 3 ∧ 3 < 22 at hj; omega
    have h4 : j ≠ 4 := by intro h; subst j; change 12 ≤ 4 ∧ 4 < 22 at hj; omega
    have h5 : j ≠ 5 := by intro h; subst j; change 12 ≤ 5 ∧ 5 < 22 at hj; omega
    have h45 : j ≠ 45 := by intro h; subst j; change 12 ≤ 45 ∧ 45 < 22 at hj; omega
    simp [inputState, h1, h2, h3, h4, h5, h45]
  · rfl

def sourceCharge (r Q delta D E : ℕ) : ℕ :=
  let rows := AssignmentAlphabetSemantics.wordBytes r Q
  (60 * (r + 1) ^ 2 + 1) +
  (TupleProgram.powerCost (OneHotAlphabetProgram.rows 0 r) Q [[]] + 9) +
  (9 * (rows.headD []).length + 10) +
  (9 * (rows.map List.length).sum + 6 * rows.length + 7) +
  (Q * (7 * r + 7) + 3) + (7 * delta + 7) +
  (14 * (delta + 1) + 10) +
  ((delta + 1) * (7 * D + 7) + 3 + (7 * E + 5)) +
  (AssignmentSeedRange.budget (seedCount delta D E) + 1)

def sourceBudget (r Q delta D E B : ℕ) : ℕ :=
  sourceCharge r Q delta D E + 5000 * (B + 1)

/-- The complete fixed producer, including concrete record extraction and
range generation. The only semantic witness chooses names for the actual
emitted word bytes; it is not supplied to the executable program. -/
theorem command_eval_measured (regs : Fin 16 → Bool) (r Q delta D E B : ℕ)
    (pairs : List Bool) (hr : 0 < r) (hB : 1 ≤ B)
    (ha : Within (inputState regs r Q delta D E pairs) B)
    (hcolor : (ProgramEncoding.encodeRecords (OneHotAlphabetProgram.rows 0 r)).length ≤ B)
    (hwords : (ProgramEncoding.encodeRecords (AssignmentAlphabetSemantics.wordBytes r Q)).length ≤ B)
    (hfirst : ((AssignmentAlphabetSemantics.wordBytes r Q).headD []).length ≤ B)
    (hflat : (AssignmentAlphabetSemantics.wordBytes r Q).flatten.length ≤ B)
    (hwidth : Q * r ≤ B) (hdelta : delta + 1 ≤ B) (hdepth : 2 * (delta + 1) ≤ B)
    (hseed : seedCount delta D E ≤ B)
    (hseeds : (AssignmentSeedRange.seedRecords (seedCount delta D E)).length ≤ B) :
    ∃ ticks, ticks ≤ sourceBudget r Q delta D E B ∧
      Eval command ticks (inputState regs r Q delta D E pairs)
      (outputState r Q delta D E pairs) := by
  let a := inputState regs r Q delta D E pairs
  obtain ⟨t1, a1, he1, hs1, hc1, ht1⟩ := colorAlphabet_eval a r (input_clean regs r Q delta D E pairs) rfl
  have hb1 := within_of_update a a1 7 _ B ha hcolor hs1
  have hn1 := ht1 B ha hcolor hB
  obtain ⟨t2, a2, he2, hs2, hc2, ht2⟩ := wordAlphabet_eval a1 r Q hc1
    (by simp [hs1]) (by simp [hs1, a, inputState])
  have hb2 := within_of_update a1 a2 30 _ B hb1 hwords hs2
  have hn2 := ht2 B hb1 hwords hB
  obtain ⟨w, tail, hw, _, _⟩ := AssignmentAlphabetSemantics.wordBytes_order hr Q
  have hbytes : AssignmentAlphabetSemantics.wordBytes r Q =
      ReadPlan.encodeWord w :: tail.map ReadPlan.encodeWord := hw.symm
  have hhead : (AssignmentAlphabetSemantics.wordBytes r Q).headD [] = ReadPlan.encodeWord w := by
    simp [hbytes]
  have hwlen : (ReadPlan.encodeWord w).length ≤ B := by simpa [hbytes] using hfirst
  obtain ⟨t3, a3, he3, hs3, hc3, ht3⟩ := firstWord_eval a2 (ReadPlan.encodeWord w)
    (tail.map ReadPlan.encodeWord) hc2 (by simp [hs2, hbytes])
  have hb3 := within_of_update a2 a3 0 _ B hb2 hwlen hs3
  have hn3 := ht3 B hb2 hwlen hB
  obtain ⟨t4, a4, he4, hs4, hc4, ht4⟩ := packedAlphabet_eval a3
    (AssignmentAlphabetSemantics.wordBytes r Q) hc3 (by simp [hs3, hs2])
  have hb4 := within_of_update a3 a4 9 _ B hb3 hflat hs4
  have hn4 := ht4 B hb3 hflat hB
  have hwlen' : (unary (Q * r)).length ≤ B := by simpa using hwidth
  obtain ⟨t5, a5, he5, hs5, hc5, ht5⟩ := repeat_eval a4 1 2 10 r Q hc4
    (by simp [hs4, hs3, hs2, hs1, a, inputState])
    (by simp [hs4, hs3, hs2, hs1, a, inputState])
    (by decide) (by decide) (by simp) (by decide)
  have hb5 := within_of_update a4 a5 10 _ B hb4 hwlen' hs5
  have hn5 := ht5 B hb4 hwlen' hB
  have hdlen : (unary (delta + 1)).length ≤ B := by simpa using hdelta
  obtain ⟨t6, a6, he6, hs6, hc6, ht6⟩ := deltaPlusOne_eval a5 delta hc5
    (by simp [hs5, hs4, hs3, hs2, hs1, a, inputState])
    (by simp [hs5, hs4, hs3, hs2, hs1, a, inputState])
  have hb6 := within_of_update a5 a6 6 _ B hb5 hdlen hs6
  have hn6 := ht6 B hb5 hdlen hB
  have hdepthlen : (unary (2 * (delta + 1))).length ≤ B := by simpa using hdepth
  obtain ⟨t7, a7, he7, hs7, hc7, ht7⟩ := depth_eval a6 (delta + 1) hc6
    (by simp [hs6]) (by simp [hs6, hs5, hs4, hs3, hs2, hs1, a, inputState])
  have hb7 := within_of_update a6 a7 34 _ B hb6 hdepthlen hs7
  have hn7 := ht7 B hb6 hdepthlen hB
  have hseedlen : (unary (seedCount delta D E)).length ≤ B := by simpa using hseed
  obtain ⟨t8, a8, he8, hs8, hc8, ht8⟩ := seedSize_eval a7 delta D E hc7
    (by simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, a, inputState])
    (by simp [hs7, hs6])
    (by simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, a, inputState])
  have hb8 := within_of_update a7 a8 47 _ B hb7 hseedlen hs8
  have hn8 := ht8 B hb7 hseedlen hB
  obtain ⟨t9, a9, he9, hs9, _, ht9⟩ := seedRange_eval a8 (seedCount delta D E) hc8 (by simp [hs8])
  have hb9 := within_of_update a8 a9 46 _ B hb8 hseeds hs9
  have hn9 := ht9 B hb8 hseeds hB
  let ac := clearManyState [1, 2, 3, 4, 5, 6, 7] a9
  let af := resetManyState (List.finRange 16) ac
  have he10 := (clearMany_eval [1, 2, 3, 4, 5, 6, 7] a9).seq
    (resetMany_eval (List.finRange 16) ac)
  have haf : af = outputState r Q delta D E pairs := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      change (resetManyState (List.finRange 16) ac).regs j = false
      rw [resetMany_regs]
      simp
    · funext j
      change (resetManyState (List.finRange 16) ac).stacks j = _
      rw [resetMany_stacks]
      change (clearManyState [1, 2, 3, 4, 5, 6, 7] a9).stacks j = _
      rw [clearMany_stacks]
      fin_cases j <;> simp [hs9, hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, a,
        inputState,
        context, hbytes, AssignmentInitProgram.unary]
  change Eval cleanup _ a9 af at he10
  rw [haf] at he10
  refine ⟨_, ?_, he1.seq (he2.seq (he3.seq (he4.seq (he5.seq (he6.seq (he7.seq
    (he8.seq (he9.seq he10))))))))⟩
  have hcleanup := (clearMany_bound [1, 2, 3, 4, 5, 6, 7] a9 B hb9).2
  simp only [List.length_cons, List.length_nil, List.length_finRange] at hcleanup ⊢
  simp only [sourceBudget, sourceCharge, hhead]
  omega

/-- Explicit data-size envelope, including generated arrays. It is assertion
notation only; no bound or table is passed to the machine. -/
def extent (r Q delta D E : ℕ) (pairs : List Bool) : ℕ :=
  let rows := AssignmentAlphabetSemantics.wordBytes r Q
  1 + r + Q + delta + D + E + (delta + 1) + 2 * (delta + 1) + Q * r +
    seedCount delta D E + r ^ Q +
    (ProgramEncoding.encodeRecords (OneHotAlphabetProgram.rows 0 r)).length +
    (ProgramEncoding.encodeRecords rows).length + (rows.headD []).length + rows.flatten.length +
    (AssignmentSeedRange.seedRecords (seedCount delta D E)).length + pairs.length

def budget (r Q delta D E : ℕ) (pairs : List Bool) : ℕ :=
  sourceBudget r Q delta D E (extent r Q delta D E pairs)

/-- A closed bound containing only runtime parameter values and input size. -/
def sizeBound (r Q delta D E inputBits : ℕ) : ℕ :=
  let M := seedCount delta D E
  1 + r + Q + delta + D + E + (delta + 1) + 2 * (delta + 1) + Q * r +
    M + r ^ Q + (1 + (2 * r + 2) * r) +
    (1 + (2 * (Q * r) + 2) * r ^ Q) + Q * r + r ^ Q * (Q * r) +
    (1 + (2 * M + 2) * M) + inputBits

theorem extent_le_sizeBound (r Q delta D E : ℕ) (pairs : List Bool) (hr : 0 < r) :
    extent r Q delta D E pairs ≤ sizeBound r Q delta D E pairs.length := by
  have hc : ∀ bits ∈ OneHotAlphabetProgram.rows 0 r, bits.length ≤ r := by
    intro bits hb
    rw [AssignmentAlphabetSemantics.rows_eq_alphabet] at hb
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    simp [AssignmentAlphabetSemantics.oneHot]
  have hclen : (OneHotAlphabetProgram.rows 0 r).length = r := by
    simp [AssignmentAlphabetSemantics.rows_eq_alphabet]
  have hcolor := ProgramEncoding.encodeRecords_length_le (OneHotAlphabetProgram.rows 0 r) r hc
  rw [hclen] at hcolor
  have hw : ∀ bits ∈ AssignmentAlphabetSemantics.wordBytes r Q, bits.length ≤ Q * r :=
    fun bits hb => (AssignmentAlphabetSemantics.wordBytes_width hr bits hb).le
  have hwords := ProgramEncoding.encodeRecords_length_le
    (AssignmentAlphabetSemantics.wordBytes r Q) (Q * r) hw
  rw [AssignmentAlphabetSemantics.wordBytes_length] at hwords
  have hvolume := PairScoreBounds.volume_le (AssignmentAlphabetSemantics.wordBytes r Q) (Q * r) hw
  rw [AssignmentAlphabetSemantics.wordBytes_length] at hvolume
  have hflat : (AssignmentAlphabetSemantics.wordBytes r Q).flatten.length ≤ r ^ Q * (Q * r) := by
    simpa only [List.length_flatten, PairScoreBounds.volume] using hvolume
  have hhead : ((AssignmentAlphabetSemantics.wordBytes r Q).headD []).length = Q * r := by
    obtain ⟨a, tail, he, _, _⟩ := AssignmentAlphabetSemantics.wordBytes_order hr Q
    rw [← he]
    simp [ReadPlan.encodeWord_length, ReadPlan.wordWidth]
  have hseeds := ProgramEncoding.encodeRecords_length_le
    ((List.range (seedCount delta D E)).map unary) (seedCount delta D E) (by
      intro bits hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
      simpa using (List.mem_range.mp hi).le)
  simp only [List.length_map, List.length_range] at hseeds
  change (AssignmentSeedRange.seedRecords (seedCount delta D E)).length ≤ _ at hseeds
  dsimp only [extent, sizeBound]
  rw [hhead]
  omega

theorem command_eval (regs : Fin 16 → Bool) (r Q delta D E : ℕ)
    (pairs : List Bool) (hr : 0 < r) :
    ∃ ticks, ticks ≤ budget r Q delta D E pairs ∧
      Eval command ticks (inputState regs r Q delta D E pairs)
        (outputState r Q delta D E pairs) := by
  apply command_eval_measured regs r Q delta D E (extent r Q delta D E pairs) pairs hr
  · dsimp only [extent]
    omega
  · intro j
    dsimp only [inputState]
    split_ifs <;> (try simp only [List.length_replicate, List.length_nil]) <;>
      dsimp only [extent] <;> omega
  all_goals dsimp only [extent]; omega

theorem budget_le (r Q delta D E : ℕ) (pairs : List Bool) (hr : 0 < r) :
    budget r Q delta D E pairs ≤ 20000 * (extent r Q delta D E pairs + 1) ^ 4 := by
  let B := extent r Q delta D E pairs
  let T := B + 1
  have hrB : r ≤ B := by dsimp [B, extent]; omega
  have hQB : Q ≤ B := by dsimp [B, extent]; omega
  have hdB : delta ≤ B := by dsimp [B, extent]; omega
  have hd1B : delta + 1 ≤ B := by dsimp [B, extent]; omega
  have hDB : D ≤ B := by dsimp [B, extent]; omega
  have hEB : E ≤ B := by dsimp [B, extent]; omega
  have hMB : seedCount delta D E ≤ B := by dsimp [B, extent]; omega
  have hpowB : r ^ Q ≤ B := by dsimp [B, extent]; omega
  have hhead : ((AssignmentAlphabetSemantics.wordBytes r Q).headD []).length ≤ B := by
    dsimp [B, extent]; omega
  have hflat : ((AssignmentAlphabetSemantics.wordBytes r Q).map List.length).sum ≤ B := by
    have h : (AssignmentAlphabetSemantics.wordBytes r Q).flatten.length ≤ B := by
      dsimp [B, extent]; omega
    simpa only [List.length_flatten] using h
  have hcount : (AssignmentAlphabetSemantics.wordBytes r Q).length ≤ B := by
    simpa using hpowB
  have hcolorlen : (OneHotAlphabetProgram.rows 0 r).length = r := by
    rw [AssignmentAlphabetSemantics.rows_eq_alphabet]
    simp
  have hcolorwidth : ∀ bits ∈ OneHotAlphabetProgram.rows 0 r, bits.length ≤ r := by
    intro bits hb
    rw [AssignmentAlphabetSemantics.rows_eq_alphabet] at hb
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hb
    simp [AssignmentAlphabetSemantics.oneHot]
  have hpower := PairScoreBounds.generated_powerCost_le (OneHotAlphabetProgram.rows 0 r) Q r
    (by rw [hcolorlen]; omega) hcolorwidth
  rw [hcolorlen] at hpower
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hrT : r + 1 ≤ T := by dsimp [T]; omega
  have hQT : Q + 1 ≤ T := by dsimp [T]; omega
  have hDT : D + 1 ≤ T := by dsimp [T]; omega
  have hMT : seedCount delta D E + 1 ≤ T := by dsimp [T]; omega
  have hlast : (Q + 1) * r + 1 ≤ T ^ 2 := by
    have hh := Nat.mul_le_mul hQT hrB
    dsimp [T] at hh ⊢
    nlinarith only [hh]
  have hpower' : TupleProgram.powerCost (OneHotAlphabetProgram.rows 0 r) Q [[]] ≤ 800 * T ^ 4 := by
    calc
      _ ≤ 800 * T * T * T ^ 2 := hpower.trans (by gcongr ; omega)
      _ = _ := by ring
  have hcolor : 60 * (r + 1) ^ 2 ≤ 60 * T ^ 2 := by gcongr
  have hseed : AssignmentSeedRange.budget (seedCount delta D E) ≤ 60 * T ^ 2 :=
    (AssignmentSeedRange.budget_le _).trans (by gcongr)
  have hwidth : Q * (7 * r + 7) ≤ 7 * T ^ 2 := by
    calc
      _ = 7 * Q * (r + 1) := by ring
      _ ≤ 7 * T * T := by gcongr ; omega
      _ = _ := by ring
  have hproduct : (delta + 1) * (7 * D + 7) ≤ 7 * T ^ 2 := by
    calc
      _ = 7 * (delta + 1) * (D + 1) := by ring
      _ ≤ 7 * T * T := by gcongr ; omega
      _ = _ := by ring
  have hT2 : T ≤ T ^ 2 := le_self_pow hT (by decide)
  have hT4 : T ^ 2 ≤ T ^ 4 := pow_le_pow_right' hT (by decide)
  have hcharge : sourceCharge r Q delta D E ≤
      800 * T ^ 4 + 134 * T ^ 2 + 52 * B + 56 := by
    dsimp only [sourceCharge]
    omega
  have hBT : B + 1 = T := rfl
  change sourceCharge r Q delta D E + 5000 * T ≤ 20000 * T ^ 4
  omega

theorem program_runsIn (regs : Fin 16 → Bool) (r Q delta D E : ℕ)
    (pairs : List Bool) (hr : 0 < r) :
    RunsIn program (budget r Q delta D E pairs + 1)
      ((inputState regs r Q delta D E pairs).withPC (some program.entry))
      ((outputState r Q delta D E pairs).withPC none) := by
  obtain ⟨ticks, hbound, ht⟩ := command_eval regs r Q delta D E pairs hr
  exact ⟨ticks + 1, Nat.add_le_add_right hbound 1, compiled_halt_trace ht 1 30⟩

theorem program_runsIn_closed (regs : Fin 16 → Bool) (r Q delta D E : ℕ)
    (pairs : List Bool) (hr : 0 < r) :
    RunsIn program (20000 * (sizeBound r Q delta D E pairs.length + 1) ^ 4 + 1)
      ((inputState regs r Q delta D E pairs).withPC (some program.entry))
      ((outputState r Q delta D E pairs).withPC none) := by
  apply (program_runsIn regs r Q delta D E pairs hr).mono
  apply Nat.add_le_add_right
  exact (budget_le r Q delta D E pairs hr).trans
    (Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left
      (Nat.add_le_add_right (extent_le_sizeBound r Q delta D E pairs hr) 1) 4))

theorem program_primitive (regs : Fin 16 → Bool) (r Q delta D E : ℕ)
    (pairs : List Bool) (hr : 0 < r) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program *
        (20000 * (sizeBound r Q delta D E pairs.length + 1) ^ 4 + 1))
      (primitiveCfg program ((inputState regs r Q delta D E pairs).withPC (some program.entry)))
      (primitiveCfg program ((outputState r Q delta D E pairs).withPC none)) :=
  primitive_execution program (program_runsIn_closed regs r Q delta D E pairs hr)

theorem program_trace (regs : Fin 16 → Bool) (r Q delta D E : ℕ)
    (pairs : List Bool) (hr : 0 < r) :
    ∃ ticks, Trace program ticks
      ((inputState regs r Q delta D E pairs).withPC (some program.entry))
      ((outputState r Q delta D E pairs).withPC none) := by
  obtain ⟨ticks, _, ht⟩ := command_eval regs r Q delta D E pairs hr
  exact ⟨ticks + 1, compiled_halt_trace ht 1 30⟩

theorem context_word_order (r Q delta D E : ℕ) (pairs : List Bool) (hr : 0 < r) :
    ∃ a : MulticolorTypes.Word r Q, ∃ tail : List (MulticolorTypes.Word r Q),
      (a :: tail).Nodup ∧ (∀ w, w ∈ a :: tail) ∧
      (context r Q delta D E pairs).defaultWord = ReadPlan.encodeWord a ∧
      (context r Q delta D E pairs).packedAlphabet =
        ((a :: tail).map ReadPlan.encodeWord).flatten ∧
      (context r Q delta D E pairs).alphabetRecords =
        ProgramEncoding.encodeRecords ((a :: tail).map ReadPlan.encodeWord) ∧
      (context r Q delta D E pairs).width = unary (ReadPlan.encodeWord a).length := by
  obtain ⟨a, tail, he, hn, hf⟩ := AssignmentAlphabetSemantics.wordBytes_order hr Q
  refine ⟨a, tail, hn, hf, ?_, ?_, ?_, ?_⟩
  · simp [context, ← he]
  · simp only [context, he]
  · simp only [context, he]
  · simp [context, ReadPlan.encodeWord_length, ReadPlan.wordWidth]

end SubexponentialSAT.Subexp.AssignmentInputProgram

end OAI.Algorithms
