import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidates
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
import OAI.Algorithms.SubexponentialSAT.ModularRingPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramStorage
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.ABI

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog

/-- The original argmin bank occupies ports 0 through 8. Port 9 is the
persistent current candidate and port 10 is preserving-copy scratch. -/
def core : HashSelectProgram.Ports 8 11 where
  register := id
  stack := Fin.castAdd 2
  register_injective := Function.injective_id
  stack_injective := Fin.castAdd_injective 9 2

def data (regs : Fin 8 → Bool) (next best : BinaryArgmin.Entry)
    (queue counter : List Bool) : State 8 11 :=
  ⟨regs, ![next.payload, next.score, best.payload, best.score,
    [], [], [], [], queue, counter, []]⟩

private theorem core_state (frameRegs regs : Fin 8 → Bool)
    (next best : BinaryArgmin.Entry) (queue counter : List Bool) :
    HashSelectProgram.state core (data frameRegs BinaryArgmin.empty BinaryArgmin.empty [] counter)
      regs next best queue = data regs next best queue counter := by
  unfold HashSelectProgram.state
  apply SubexpScanPrimitives.embedState_eq core.register core.stack
    core.register_injective core.stack_injective
  · intro i; rfl
  · intro i; fin_cases i <;> rfl
  · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    have hj9 : 9 ≤ j.val := by
      by_contra hn
      have hlt : j.val < 9 := by omega
      exact hj ⟨⟨j.val, hlt⟩, by apply Fin.ext; rfl⟩
    fin_cases j <;> simp_all [data]

/-- One bounded current-record load. The entire family is never an input. -/
def load : Cmd 8 11 :=
  .seq (.call (StackRoutines.copyProgram 9 8 10 0 1))
    (.seq (HashSelectProgram.parse core) (.call (StackRoutines.clearProgram 8 0 1)))

theorem load_eval (regs : Fin 8 → Bool) (best : BinaryArgmin.Entry) (word : List Bool) :
    ∃ regs', Eval load (20 * word.length + 38)
      (data regs BinaryArgmin.empty best [] (Encoding.encodeList id [word]))
      (data regs' ⟨word.reverse, []⟩ best [] (Encoding.encodeList id [word])) := by
  let counter := Encoding.encodeList id [word]
  let a := data regs BinaryArgmin.empty best [] counter
  let regs₁ := readRegs regs 0 1 none
  have hcopy := Subexp.TupleProgram.copy_eval (9 : Fin 11) 8 10 (0 : Fin 8) 1
    (by decide) (by decide) (by decide) (by decide) a rfl
  have hcopyOut : (⟨readRegs a.regs 0 1 none,
      StackRoutines.copyStacks 9 8 a.stacks⟩ : State 8 11) =
      data regs₁ BinaryArgmin.empty best counter counter := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a, data, StackRoutines.copyStacks]
  rw [hcopyOut] at hcopy
  have hqueue : counter = HashSelectProgram.candidateEncoding [word.reverse] := by
    simp [counter, HashSelectProgram.candidateEncoding, Encoding.encodeList]
  let frame := data regs BinaryArgmin.empty BinaryArgmin.empty [] counter
  obtain ⟨regs₂, _, hparse⟩ := HashSelectProgram.parse_cons core frame
    word.reverse [] best regs₁
  rw [core_state, core_state, ← hqueue] at hparse
  have hclear := Subexp.TupleProgram.clear_eval (8 : Fin 11) (0 : Fin 8) 1
    (data regs₂ ⟨word.reverse, []⟩ best [false] counter)
  have hclearOut : (⟨readRegs regs₂ 0 1 none,
      StackRoutines.clearStacks 8 (data regs₂ ⟨word.reverse, []⟩ best [false] counter).stacks⟩ :
      State 8 11) = data (readRegs regs₂ 0 1 none) ⟨word.reverse, []⟩ best [] counter := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [data, StackRoutines.clearStacks]
  change Eval _ 5 _ _ at hclear
  change Eval _ 5 _ (⟨readRegs regs₂ 0 1 none, _⟩ : State 8 11) at hclear
  rw [hclearOut] at hclear
  refine ⟨readRegs regs₂ 0 1 none, ?_⟩
  have hlen : counter.length = 2 * word.length + 3 := by
    simp [counter, Encoding.encodeList, Encoding.length_frame]
  have h := hcopy.seq (hparse.seq hclear)
  change Eval load (7 * counter.length + 5 + (6 * word.reverse.length + 7 + 5))
    (data regs BinaryArgmin.empty best [] counter)
    (data (readRegs regs₂ 0 1 none) ⟨word.reverse, []⟩ best [] counter) at h
  rw [List.length_reverse, hlen] at h
  convert h using 1
  omega

/-- Actual fixed finite table for one candidate load, suitable for relocation
into the selector bank. Its time is polynomial in one retained candidate. -/
def loadProgram := compiled load 9 0

theorem load_trace (regs : Fin 8 → Bool) (best : BinaryArgmin.Entry) (word : List Bool) :
    ∃ regs', Trace loadProgram (20 * word.length + 39)
      ((data regs BinaryArgmin.empty best [] (Encoding.encodeList id [word])).withPC
        (some loadProgram.entry))
      ((data regs' ⟨word.reverse, []⟩ best [] (Encoding.encodeList id [word])).withPC none) := by
  obtain ⟨regs', he⟩ := load_eval regs best word
  exact ⟨regs', by simpa [loadProgram, Nat.add_assoc] using compiled_halt_trace he 9 0⟩

/-- Every source prefix, including parser and copy microsteps, counts all
stacks. This local estimate is independent of the number of candidates. -/
theorem load_prefix_space (regs : Fin 8 → Bool) (best : BinaryArgmin.Entry)
    (word : List Bool) (B : ℕ)
    (hB : dataBits ((data regs BinaryArgmin.empty best []
      (Encoding.encodeList id [word])).withPC (some loadProgram.entry)) ≤ B) :
    ∀ t c, t ≤ 20 * word.length + 39 →
      Trace loadProgram t ((data regs BinaryArgmin.empty best []
        (Encoding.encodeList id [word])).withPC (some loadProgram.entry)) c →
      ∀ i, (c.stacks i).length ≤ B + (20 * word.length + 39) :=
  StructuredSpace.local_stack_bound loadProgram hB


/-- The existing fixed addition-and-reduction table also canonicalizes an
arbitrary word: its second summand is the empty representation of zero. -/
theorem normalize_digit_runs (regs : Fin 8 → Bool) (word modulus : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ word.length) :
    ∃ rf, RunsIn ModularRingPrograms.wordAddProgram
      (1000 * (modulus.length + word.length + 1) ^ 2)
      ⟨some 0, regs, ModularRingPrograms.extendSeven
        (ModularRingPrograms.scalarInput word [] modulus) []⟩
      ⟨none, rf, ModularRingPrograms.extendSeven
        (ModularDivisionPrograms.resting
          (SubexpLiftRing.fixedBits word.length
            (BinaryArithmetic.toNat word % BinaryArithmetic.toNat modulus)) modulus []) []⟩ := by
  obtain ⟨r, output, hr, hlen, hv⟩ := ModularRingPrograms.addMod_value
    (readRegs regs 1 3 none) word [] modulus hm
  obtain ⟨rf, ht⟩ := ModularRingPrograms.canonical_execute
    ModularRingPrograms.addModProgram regs r word [] modulus output
    (600 * (modulus.length + word.length + 1) ^ 2) hr
  have hsmall : BinaryArithmetic.toNat output < 2 ^ word.length := by
    rw [hv]
    simpa using (Nat.mod_lt (BinaryArithmetic.toNat word) hm).trans_le hcapacity
  have hvalue : BinaryArithmetic.toNat (ModularArithmetic.padTo word output) =
      BinaryArithmetic.toNat word % BinaryArithmetic.toNat modulus := by
    rw [ModularRingPrograms.padTo_value_of_lt _ _ hsmall, hv]
    simp
  have hout : ModularArithmetic.padTo word output =
      SubexpLiftRing.fixedBits word.length
        (BinaryArithmetic.toNat word % BinaryArithmetic.toNat modulus) := by
    apply ExecCNFTupleEnumeration.word_eq_of_length_value
    · simp [ModularArithmetic.padTo_length]
    · rw [CounterPrograms.value_eq_toNat, CounterPrograms.value_eq_toNat, hvalue,
        SubexpLiftRing.toNat_fixedBits_of_lt _ _ ((Nat.mod_lt _ hm).trans_le hcapacity)]
  rw [hout] at ht
  refine ⟨rf, ht.mono ?_⟩
  simp only [List.length_nil, Nat.add_zero] at hlen ⊢
  have hsq : modulus.length + word.length + 1 ≤
      (modulus.length + word.length + 1) ^ 2 := by
    nlinarith
  nlinarith

namespace Normalize

open OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

/-- Ports 0..7 are the existing modular arithmetic bank. The remaining
ports hold unread bits, the accumulated normalized payload and take scratch. -/
def state (regs : Fin 8 → Bool) (chunk modulus unread result : List Bool) : State 8 12 :=
  ⟨regs, ![chunk, [], [], [], [], modulus, [], [], unread, result, [], []]⟩

def arithmeticPorts : Fin 8 → Fin 12 := Fin.castAdd 4

def digit : Cmd 8 12 := .call
  (ProgramLinking.liftProgram ModularRingPrograms.wordAddProgram id arithmeticPorts)

private theorem embed_arithmetic (regs rf : Fin 8 → Bool)
    (chunk modulus unread result : List Bool) :
    embedState id arithmeticPorts (state regs [] modulus unread result)
      ⟨rf, ModularRingPrograms.extendSeven
        (ModularDivisionPrograms.resting chunk modulus []) []⟩ =
      state rf chunk modulus unread result := by
  apply SubexpScanPrimitives.embedState_eq id arithmeticPorts
    Function.injective_id (Fin.castAdd_injective 8 4)
  · intros; rfl
  · intro i; fin_cases i <;> rfl
  · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
  · intro j hj
    have hj8 : 8 ≤ j.val := by
      by_contra hn
      have hlt : j.val < 8 := by omega
      exact hj ⟨⟨j.val, hlt⟩, by apply Fin.ext; rfl⟩
    fin_cases j <;> simp_all [state]

theorem digit_eval (regs : Fin 8 → Bool) (chunk modulus unread result : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ chunk.length) :
    ∃ t ≤ 1000 * (modulus.length + chunk.length + 1) ^ 2, ∃ rf,
      Eval digit t (state regs chunk modulus unread result)
        (state rf (SubexpLiftRing.fixedBits chunk.length
          (BinaryArithmetic.toNat chunk % BinaryArithmetic.toNat modulus))
          modulus unread result) := by
  obtain ⟨rf, t, ht, he⟩ := normalize_digit_runs regs chunk modulus hm hcapacity
  have h := eval_call_lifted ModularRingPrograms.wordAddProgram id arithmeticPorts
    (state regs [] modulus unread result) Function.injective_id
    (Fin.castAdd_injective 8 4)
    (a := ⟨regs, ModularRingPrograms.extendSeven
      (ModularRingPrograms.scalarInput chunk [] modulus) []⟩)
    (b := ⟨rf, ModularRingPrograms.extendSeven
      (ModularDivisionPrograms.resting (SubexpLiftRing.fixedBits chunk.length
        (BinaryArithmetic.toNat chunk % BinaryArithmetic.toNat modulus)) modulus []) []⟩) he
  have hin : ModularRingPrograms.scalarInput chunk [] modulus =
      ModularDivisionPrograms.resting chunk modulus [] := rfl
  simp only [hin] at h
  rw [embed_arithmetic, embed_arithmetic] at h
  exact ⟨t, ht, rf, h⟩

def take : Cmd 8 12 := takeWord 5 10 11 8 0 0 1

theorem take_eval (regs : Fin 8 → Bool) (chunk rest modulus result : List Bool)
    (hw : modulus.length = chunk.length) :
    Eval take (14 * chunk.length + 11)
      (state regs [] modulus (chunk ++ rest) result)
      (state (readRegs regs 0 1 none) chunk modulus rest result) := by
  have h := takeWord_eval (state regs [] modulus (chunk ++ rest) result)
    5 10 11 8 0 0 1 (by decide) (by decide) chunk rest rfl rfl rfl hw
  convert h using 1
  · rfl
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [state]

def emit : Cmd 8 12 := .call (StackRoutines.transferProgram 0 9 0 1)

theorem emit_eval (regs : Fin 8 → Bool) (chunk modulus unread result : List Bool) :
    Eval emit (3 * chunk.length + 3) (state regs chunk modulus unread result)
      (state (readRegs regs 0 1 none) [] modulus unread (chunk.reverse ++ result)) := by
  have h := SubexpScanPrimitives.transfer_eval
    (state regs chunk modulus unread result) 0 9 0 1 (by decide) (by decide)
  convert h using 1
  · rfl
  · simp [state]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [state, StackRoutines.transferStacks]

def step : Cmd 8 12 := .seq take (.seq digit emit)

def canonicalDigit (modulus chunk : List Bool) : List Bool :=
  SubexpLiftRing.fixedBits chunk.length
    (BinaryArithmetic.toNat chunk % BinaryArithmetic.toNat modulus)

theorem step_eval (regs : Fin 8 → Bool) (chunk rest modulus result : List Bool)
    (hw : modulus.length = chunk.length) (hm : 0 < BinaryArithmetic.toNat modulus)
    (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ chunk.length) :
    ∃ t ≤ 5000 * (modulus.length + 1) ^ 2, ∃ rf,
      Eval step t (state regs [] modulus (chunk ++ rest) result)
        (state rf [] modulus rest ((canonicalDigit modulus chunk).reverse ++ result)) := by
  have htake := take_eval regs chunk rest modulus result hw
  obtain ⟨t, ht, rf, hdigit⟩ := digit_eval (readRegs regs 0 1 none)
    chunk modulus rest result hm hcapacity
  have hemit := emit_eval rf (canonicalDigit modulus chunk) modulus rest result
  refine ⟨_, ?_, readRegs rf 0 1 none, htake.seq (hdigit.seq hemit)⟩
  simp only [canonicalDigit, SubexpLiftRing.fixedBits_length]
  rw [← hw] at ht ⊢
  nlinarith


def probe : Cmd 8 12 := .base (.atom (.peek 8 0 1))

theorem probe_eval (regs : Fin 8 → Bool) (modulus unread result : List Bool) :
    Eval probe 1 (state regs [] modulus unread result)
      (state (readRegs regs 0 1 unread.head?) [] modulus unread result) := by
  have h := Eval.base (StructuredProgram.Eval.atom
    (StructuredProgram.Atom.peek (r := 8) (s := 12) 8 0 1)
    (state regs [] modulus unread result))
  exact h

def loop : Cmd 8 12 := .while 1 (.seq step probe)

theorem loop_eval (modulus : List Bool) (hm : 0 < BinaryArithmetic.toNat modulus)
    (words : List (List Bool)) (hw : ∀ word ∈ words, word.length = modulus.length)
    (regs : Fin 8 → Bool) (result : List Bool)
    (hf : regs 1 = words.flatten.head?.isSome) :
    ∃ t ≤ words.length * (5000 * (modulus.length + 1) ^ 2 + 4) + 1,
      ∃ rf, Eval loop t (state regs [] modulus words.flatten result)
        (state rf [] modulus [] ((words.map (canonicalDigit modulus)).flatten.reverse ++ result)) := by
  have hwpos : 0 < modulus.length := by
    cases modulus with
    | nil => simp [BinaryArithmetic.toNat] at hm
    | cons b bs => simp
  induction words generalizing regs result with
  | nil =>
    exact ⟨1, by simp, regs, by simpa [loop] using
      (Eval.while_false (by simpa [state] using hf) :
        Eval (.while 1 (.seq step probe)) 1 (state regs [] modulus [] result)
          (state regs [] modulus [] result))⟩
  | cons word words ih =>
    have hword := hw word (by simp)
    have hwords : ∀ word ∈ words, word.length = modulus.length :=
      fun word h => hw word (by simp [h])
    have hwne : word ≠ [] := by intro hz; simp [hz] at hword; omega
    have hflag : regs 1 = true := by
      rw [hf]
      cases word with
      | nil => contradiction
      | cons bit rest => rfl
    have hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ word.length := by
      rw [hword]
      exact (ModularArithmetic.toNat_lt_pow_length modulus).le
    obtain ⟨a, ha, ra, he⟩ := step_eval regs word words.flatten modulus result
      hword.symm hm hcapacity
    let nextResult := (canonicalDigit modulus word).reverse ++ result
    have hp := probe_eval ra modulus words.flatten nextResult
    obtain ⟨b, hb, rb, ht⟩ := ih hwords
      (readRegs ra 0 1 words.flatten.head?) nextResult (by simp [readRegs])
    refine ⟨a + 1 + b + 1, ?_, rb, ?_⟩
    · simp only [List.length_cons]
      nlinarith
    · have h := Eval.while_true hflag (he.seq hp) ht
      simpa [loop, state, nextResult, List.flatten_cons, List.reverse_append,
        List.append_assoc] using h

/-- Normalization scans one retained payload. It has polynomial bit time;
therefore the local all-stack prefix rule applies to every invocation. -/
def command : Cmd 8 12 := .seq probe loop

theorem command_eval (modulus : List Bool) (hm : 0 < BinaryArithmetic.toNat modulus)
    (words : List (List Bool)) (hw : ∀ word ∈ words, word.length = modulus.length)
    (regs : Fin 8 → Bool) (result : List Bool) :
    ∃ t ≤ words.length * (5000 * (modulus.length + 1) ^ 2 + 4) + 4,
      ∃ rf, Eval command t (state regs [] modulus words.flatten result)
        (state rf [] modulus [] ((words.map (canonicalDigit modulus)).flatten.reverse ++ result)) := by
  have hp := probe_eval regs modulus words.flatten result
  obtain ⟨t, ht, rf, he⟩ := loop_eval modulus hm words hw
    (readRegs regs 0 1 words.flatten.head?) result (by simp [readRegs])
  exact ⟨1 + t, by omega, rf, hp.seq he⟩



def prepare : Cmd 8 12 := .call (StackRoutines.reverseProgram 8 0 1 0 1)

theorem prepare_eval (regs : Fin 8 → Bool) (modulus raw : List Bool) :
    Eval prepare (9 * raw.length + 7)
      (state regs [] modulus raw [])
      (state (readRegs regs 0 1 none) [] modulus raw.reverse []) := by
  have h := SubexpScanPrimitives.reverse_eval (state regs [] modulus raw [])
    8 0 1 0 1 (by decide) (by decide) (by decide) (by decide) rfl rfl
  convert h using 1
  · rfl
  · simp [state]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [state, StackRoutines.reverseStacks]

def normalize : Cmd 8 12 := .seq prepare command

def budget (m depth : ℕ) : ℕ :=
  9 * HashCandidates.payloadWidth m depth +
    depth * (5000 * (HashCandidates.digitWidth m + 1) ^ 2 + 4) + 11

/-- Complete current-candidate canonicalization. The modulus and all digits
are ordinary bit words; scalar division, truncation and copies are charged. -/
theorem normalize_eval {m depth : ℕ} (hm : 0 < m) (regs : Fin 8 → Bool)
    (raw modulus : List Bool) (hraw : raw.length = HashCandidates.payloadWidth m depth)
    (hwidth : modulus.length = HashCandidates.digitWidth m)
    (hmodulus : BinaryArithmetic.toNat modulus = 3 * m) :
    ∃ t ≤ budget m depth, ∃ rf,
      Eval normalize t (state regs [] modulus raw [])
        (state rf [] modulus [] (HashCandidates.normalize m depth raw)) := by
  let words := HashCandidates.chunks m depth raw
  have hwords : ∀ word ∈ words, word.length = modulus.length := by
    intro word hw
    exact (HashCandidates.chunks_width hraw word hw).trans hwidth.symm
  have hpositive : 0 < BinaryArithmetic.toNat modulus := by rw [hmodulus]; omega
  obtain ⟨t, ht, rf, he⟩ := command_eval modulus hpositive words hwords
    (readRegs regs 0 1 none) []
  have hflat : words.flatten = raw.reverse := HashCandidates.chunks_flatten hraw
  have hout : (words.map (canonicalDigit modulus)).flatten.reverse =
      HashCandidates.normalize m depth raw := by
    unfold HashCandidates.normalize
    congr 2
    apply List.map_congr_left
    intro word hw
    simp only [canonicalDigit, hmodulus, HashCandidates.chunks_width hraw word hw]
  rw [hflat, List.append_nil, hout] at he
  refine ⟨9 * raw.length + 7 + t, ?_, rf, (prepare_eval regs modulus raw).seq he⟩
  rw [hraw]
  simp only [words, HashCandidates.chunks_length, hwidth] at ht
  unfold budget
  omega

def program := compiled normalize 8 9

theorem program_runs {m depth : ℕ} (hm : 0 < m) (regs : Fin 8 → Bool)
    (raw modulus : List Bool) (hraw : raw.length = HashCandidates.payloadWidth m depth)
    (hwidth : modulus.length = HashCandidates.digitWidth m)
    (hmodulus : BinaryArithmetic.toNat modulus = 3 * m) :
    ∃ rf, RunsIn program (budget m depth + 1)
      ((state regs [] modulus raw []).withPC (some program.entry))
      ((state rf [] modulus [] (HashCandidates.normalize m depth raw)).withPC none) := by
  obtain ⟨t, ht, rf, he⟩ := normalize_eval hm regs raw modulus hraw hwidth hmodulus
  exact ⟨rf, t + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 8 9⟩

theorem prefix_space (regs : Fin 8 → Bool) (raw modulus : List Bool)
    (m depth initialBound : ℕ)
    (hB : dataBits ((state regs [] modulus raw []).withPC (some program.entry)) ≤ initialBound) :
    ∀ t c, t ≤ budget m depth + 1 →
      Trace program t ((state regs [] modulus raw []).withPC (some program.entry)) c →
      ∀ i, (c.stacks i).length ≤ initialBound + (budget m depth + 1) :=
  StructuredSpace.local_stack_bound program hB



theorem budget_polynomial (m depth : ℕ) :
    budget m depth + 1 ≤
      6000 * (depth + 1) * (HashCandidates.digitWidth m + 1) ^ 2 := by
  unfold budget HashCandidates.payloadWidth
  nlinarith [Nat.zero_le (depth * HashCandidates.digitWidth m ^ 2)]


end Normalize

namespace ZeroCounter

open OAI.Algorithms.SubexponentialSAT.Subexp.TupleProgram

/-- The retained modulus is port3; the binary depth is port2. Ports0,4,5
are scratch and port1 is the current framed counter under construction. -/
def state (regs : Fin 3 → Bool) (scan output count modulus : List Bool) : State 3 6 :=
  ⟨regs, ![scan, output, count, modulus, [], []]⟩

def pairs (n : ℕ) (tail : List Bool) : List Bool :=
  escaped (List.replicate n false) ++ tail

@[simp] theorem pairs_zero (tail : List Bool) : pairs 0 tail = tail := rfl

@[simp] theorem pairs_succ (n : ℕ) (tail : List Bool) :
    pairs (n + 1) tail = true :: false :: pairs n tail := by
  simp [pairs, List.replicate_succ]

theorem pairs_add (n k : ℕ) (tail : List Bool) :
    pairs n (pairs k tail) = pairs (n + k) tail := by
  simp only [pairs, List.replicate_add, escaped_append, List.append_assoc]

theorem framed (n : ℕ) :
    true :: pairs n [false, false] = Encoding.encodeList id [List.replicate n false] := by
  simp [pairs, Encoding.encodeList, frame_eq_escaped, List.append_assoc]

def peek : Cmd 3 6 := .base (.atom (.peek 0 0 1))

theorem peek_eval (regs : Fin 3 → Bool) (scan output count modulus : List Bool) :
    Eval peek 1 (state regs scan output count modulus)
      (state (readRegs regs 0 1 scan.head?) scan output count modulus) :=
  .base (.atom _ _)

def bit : Cmd 3 6 := .seq (.base (.atom (.pop 0 0 1)))
  (.seq (pushConst 1 0 false) (.seq (pushConst 1 0 true) peek))

theorem bit_eval (regs : Fin 3 → Bool) (b : Bool) (scan output count modulus : List Bool) :
    Eval bit 6 (state regs (b :: scan) output count modulus)
      (state (readRegs regs 0 1 scan.head?) scan (true :: false :: output) count modulus) := by
  let a := state regs (b :: scan) output count modulus
  let c := (StructuredProgram.Atom.pop (r := 3) (s := 6) 0 0 1).eval a
  let d := pushedState 1 0 false c
  let e := pushedState 1 0 true d
  have h := (Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 6) (0 : Fin 3) 1) a)).seq
    ((pushConst_eval (1 : Fin 6) (0 : Fin 3) false c).seq
      ((pushConst_eval (1 : Fin 6) (0 : Fin 3) true d).seq
        (Eval.base (StructuredProgram.Eval.atom (.peek (0 : Fin 6) (0 : Fin 3) 1) e))))
  convert h using 1
  · rfl
  · apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [a, c, d, e, state,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, readRegs]
    · funext i; fin_cases i <;> simp [a, c, d, e, state,
        StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, readRegs]

def bitsLoop : Cmd 3 6 := .while 1 bit

theorem bitsLoop_eval (regs : Fin 3 → Bool) (scan output count modulus : List Bool)
    (hf : regs 1 = scan.head?.isSome) :
    ∃ rf, Eval bitsLoop (7 * scan.length + 1)
      (state regs scan output count modulus)
      (state rf [] (pairs scan.length output) count modulus) := by
  induction scan generalizing regs output with
  | nil => exact ⟨regs, .while_false (by simpa [state] using hf)⟩
  | cons b scan ih =>
    obtain ⟨rf, ht⟩ := ih (readRegs regs 0 1 scan.head?) (true :: false :: output)
      (by simp [readRegs])
    have h := Eval.while_true (by simpa [state] using hf)
      (bit_eval regs b scan output count modulus) ht
    refine ⟨rf, ?_⟩
    have hp : pairs scan.length (true :: false :: output) = pairs (scan.length + 1) output := by
      change pairs scan.length (pairs 1 output) = _
      exact pairs_add _ _ _
    rw [hp] at h
    convert h using 1
    · rfl
    · simp only [List.length_cons]
      omega

def bits : Cmd 3 6 := .seq peek bitsLoop

theorem bits_eval (regs : Fin 3 → Bool) (scan output count modulus : List Bool) :
    ∃ rf, Eval bits (7 * scan.length + 2)
      (state regs scan output count modulus)
      (state rf [] (pairs scan.length output) count modulus) := by
  obtain ⟨rf, ht⟩ := bitsLoop_eval (readRegs regs 0 1 scan.head?) scan output count modulus
    (by simp [readRegs])
  refine ⟨rf, ?_⟩
  convert (peek_eval regs scan output count modulus).seq ht using 1
  · rfl
  · omega

def body : Cmd 3 6 := .seq (.call (StackRoutines.copyProgram 3 0 5 0 1)) bits

theorem body_eval (regs : Fin 3 → Bool) (output count modulus : List Bool) :
    ∃ rf, Eval body (14 * modulus.length + 7)
      (state regs [] output count modulus)
      (state rf [] (pairs modulus.length output) count modulus) := by
  have hc := copy_eval (3 : Fin 6) 0 5 (0 : Fin 3) 1
    (by decide) (by decide) (by decide) (by decide) (state regs [] output count modulus) rfl
  have hout : (⟨readRegs regs 0 1 none,
      StackRoutines.copyStacks 3 0 (state regs [] output count modulus).stacks⟩ : State 3 6) =
      state (readRegs regs 0 1 none) modulus output count modulus := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [state, StackRoutines.copyStacks]
  change Eval _ (7 * modulus.length + 5) _ _ at hc
  change Eval _ _ _ (⟨readRegs regs 0 1 none, _⟩ : State 3 6) at hc
  rw [hout] at hc
  obtain ⟨rf, he⟩ := bits_eval (readRegs regs 0 1 none) modulus output count modulus
  refine ⟨rf, ?_⟩
  convert hc.seq he using 1
  · rfl
  · omega

def ports : CounterForPrograms.Ports 3 6 where
  register := ⟨id, Function.injective_id⟩
  counter := 2
  scratch := 4
  counter_ne_scratch := by decide

def loop : Cmd 3 6 := CounterForPrograms.forCmd ports body

theorem loop_eval (regs : Fin 3 → Bool) (count modulus : List Bool) :
    ∃ n ≤ CounterPrograms.value count * (14 * modulus.length + 7) +
        (CounterPrograms.value count + 1) * (16 * count.length + 16),
      ∃ rf finalCount,
        Eval loop n (state regs [] [false, false] count modulus)
          (state rf [] (pairs (CounterPrograms.value count * modulus.length) [false, false])
            finalCount modulus) ∧ finalCount.length = count.length := by
  let I := fun (i : ℕ) (d : State 3 6) =>
    d.stacks 0 = [] ∧ d.stacks 1 = pairs (i * modulus.length) [false, false] ∧
      d.stacks 3 = modulus ∧ d.stacks 5 = []
  have stable : CounterForPrograms.FrameStable ports I := by
    intro i a b hab hi
    exact ⟨(hab 0 (by decide) (by decide)).symm.trans hi.1,
      (hab 1 (by decide) (by decide)).symm.trans hi.2.1,
      (hab 3 (by decide) (by decide)).symm.trans hi.2.2.1,
      (hab 5 (by decide) (by decide)).symm.trans hi.2.2.2⟩
  have spec : CounterForPrograms.BodySpec ports body I (fun _ => 14 * modulus.length + 7) := by
    intro i d hi hs _
    have hd : d = state d.regs [] (pairs (i * modulus.length) [false, false])
        (d.stacks 2) modulus := by
      apply congrArg₂ StructuredProgram.State.mk
      · rfl
      · funext j; fin_cases j <;> simp_all [I, ports]
    obtain ⟨rf, he⟩ := body_eval d.regs (pairs (i * modulus.length) [false, false])
      (d.stacks 2) modulus
    refine ⟨_, state rf [] (pairs modulus.length
      (pairs (i * modulus.length) [false, false])) (d.stacks 2) modulus,
      le_rfl, ?_, rfl, rfl, ?_⟩
    · rw [← hd] at he
      exact he
    · refine ⟨rfl, ?_, rfl, rfl⟩
      simp [state, pairs_add, Nat.add_mul, Nat.add_comm]
  obtain ⟨n, e, he, hi, _, hlen, hs, hn⟩ := CounterForPrograms.for_correct ports body I
    (fun _ => 14 * modulus.length + 7) stable spec
    (state regs [] [false, false] count modulus) rfl (by simp [I, state])
  have heq : e = state e.regs []
      (pairs (CounterPrograms.value count * modulus.length) [false, false]) (e.stacks 2) modulus := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j; fin_cases j <;> simp_all [state, I, ports]
  refine ⟨n, ?_, e.regs, e.stacks 2, ?_, hlen⟩
  · simpa [ports, state, CounterForPrograms.budgetSum_const] using hn
  · rw [heq] at he
    exact he

/-- Initialization adds the list/frame terminators; finalization adds the
leading list marker and clears the exhausted binary depth word. -/
def command : Cmd 3 6 :=
  .seq (pushConst 1 0 false) (.seq (pushConst 1 0 false)
    (.seq loop (.seq (pushConst 1 0 true) (.call (StackRoutines.clearProgram 2 0 1)))))

def budget (count modulus : List Bool) : ℕ :=
  50 * (CounterPrograms.value count + 1) * (modulus.length + count.length + 1)

theorem command_eval (regs : Fin 3 → Bool) (count modulus : List Bool) :
    ∃ n ≤ budget count modulus, ∃ rf,
      Eval command n (state regs [] [] count modulus)
        (state rf [] (Encoding.encodeList id
          [List.replicate (CounterPrograms.value count * modulus.length) false]) [] modulus) := by
  let a := state regs [] [] count modulus
  let b := pushedState 1 0 false a
  let c := pushedState 1 0 false b
  have hc : c = state c.regs [] [false, false] count modulus := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j; fin_cases j <;> simp [a, b, state]
  obtain ⟨n, hn, rf, finalCount, he, hlen⟩ := loop_eval c.regs count modulus
  rw [← hc] at he
  let d := state rf []
    (pairs (CounterPrograms.value count * modulus.length) [false, false]) finalCount modulus
  have hp := pushConst_eval (1 : Fin 6) (0 : Fin 3) true d
  have hclear := clear_eval (2 : Fin 6) (0 : Fin 3) 1 (pushedState 1 0 true d)
  have hfinal : (⟨readRegs (pushedState 1 0 true d).regs 0 1 none,
      StackRoutines.clearStacks 2 (pushedState 1 0 true d).stacks⟩ : State 3 6) =
      state (readRegs (pushedState 1 0 true d).regs 0 1 none) []
        (Encoding.encodeList id [List.replicate
          (CounterPrograms.value count * modulus.length) false]) [] modulus := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j; fin_cases j <;> simp [d, state, StackRoutines.clearStacks, framed]
  rw [hfinal] at hclear
  refine ⟨2 + (2 + (n + (2 + (2 * finalCount.length + 3)))), ?_,
    readRegs (pushedState 1 0 true d).regs 0 1 none, ?_⟩
  · rw [hlen]
    unfold budget
    nlinarith
  · exact (pushConst_eval (1 : Fin 6) (0 : Fin 3) false a).seq
      ((pushConst_eval (1 : Fin 6) (0 : Fin 3) false b).seq (he.seq (hp.seq hclear)))

def program := compiled command 2 1

theorem program_runs (regs : Fin 3 → Bool) (count modulus : List Bool) :
    ∃ rf, RunsIn program (budget count modulus + 1)
      ((state regs [] [] count modulus).withPC (some program.entry))
      ((state rf [] (Encoding.encodeList id
        [List.replicate (CounterPrograms.value count * modulus.length) false]) [] modulus).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval regs count modulus
  exact ⟨rf, n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace he 2 1⟩

theorem prefix_space (regs : Fin 3 → Bool) (count modulus : List Bool) (initialBound : ℕ)
    (hb : dataBits ((state regs [] [] count modulus).withPC (some program.entry)) ≤ initialBound) :
    ∀ t c, t ≤ budget count modulus + 1 →
      Trace program t ((state regs [] [] count modulus).withPC (some program.entry)) c →
      ∀ i, (c.stacks i).length ≤ initialBound + (budget count modulus + 1) :=
  StructuredSpace.local_stack_bound program hb

end ZeroCounter

namespace Leaf

open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram
open scoped BigOperators

def registers : Fin 8 → Fin 40 := Fin.castAdd 32

def loaderStacks : Fin 11 → Fin 896 :=
  ![768,769,770,771,772,773,774,775,776,778,779]

def loader : Cmd 40 896 := .call
  (ProgramLinking.liftProgram loadProgram registers loaderStacks)

/-- Loading changes just the candidate payload port, with all other leaf
stacks retained. The parser's bounded singleton queue is cleared. -/
theorem loader_eval (a : Data) (word : List Bool)
    (hcounter : a.stacks 778 = Encoding.encodeList id [word])
    (hclean : ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 → a.stacks (loaderStacks j) = []) :
    ∃ b, Eval loader (20 * word.length + 39) a b ∧
      b.stacks = Function.update a.stacks 768 word.reverse := by
  have hc0 := hclean 0 (by decide) (by decide) (by decide)
  have hc1 := hclean 1 (by decide) (by decide) (by decide)
  have hc4 := hclean 4 (by decide) (by decide) (by decide)
  have hc5 := hclean 5 (by decide) (by decide) (by decide)
  have hc6 := hclean 6 (by decide) (by decide) (by decide)
  have hc7 := hclean 7 (by decide) (by decide) (by decide)
  have hc8 := hclean 8 (by decide) (by decide) (by decide)
  have hc10 := hclean 10 (by decide) (by decide) (by decide)
  simp [loaderStacks] at hc0 hc1 hc4 hc5 hc6 hc7 hc8 hc10
  let d := projectState registers loaderStacks a
  let best : BinaryArgmin.Entry := ⟨a.stacks 770, a.stacks 771⟩
  have hr : Function.Injective registers := Fin.castAdd_injective 8 32
  have hs : Function.Injective loaderStacks := by decide
  have hd : d = data d.regs BinaryArgmin.empty best [] (Encoding.encodeList id [word]) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [best, loaderStacks,
        BinaryArgmin.empty, hcounter, hc0, hc1, hc4, hc5, hc6, hc7, hc8, hc10]
  obtain ⟨rf, ht⟩ := load_trace d.regs best word
  rw [← hd] at ht
  let out := data rf ⟨word.reverse, []⟩ best [] (Encoding.encodeList id [word])
  refine ⟨embedState registers loaderStacks a out,
    eval_call_from_state loadProgram registers loaderStacks a hr hs ht, ?_⟩
  have hout : out.stacks = Function.update d.stacks 0 word.reverse := by
    funext j
    fin_cases j <;> simp [out, d, projectState, data, best, loaderStacks,
      hcounter, hc1, hc4, hc5, hc6, hc7, hc8, hc10]
  change Function.extend loaderStacks out.stacks a.stacks = _
  rw [hout, ProgramLinking.extend_update hs]
  have hf : Function.extend loaderStacks d.stacks a.stacks = a.stacks :=
    congrArg StructuredProgram.State.stacks (embedState_project registers loaderStacks a hr hs)
  rw [hf]
  rfl

def normalizerStacks : Fin 12 → Fin 896 := Fin.castAdd 884

def lowPorts : List (Fin 896) := [0,1,2,3,4,5,6,7,8,9,10,11]

theorem mem_lowPorts (j : Fin 896) : j ∈ lowPorts ↔ j.val < 12 := by
  simp only [lowPorts, List.mem_cons, List.not_mem_nil, or_false, Fin.ext_iff]
  change (j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨
    j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨ j.val = 7 ∨
    j.val = 8 ∨ j.val = 9 ∨ j.val = 10 ∨ j.val = 11) ↔ j.val < 12
  omega

def clearLow : Cmd 40 896 := BankRoutines.clearCmd 767 0 1 lowPorts

def normalizer : Cmd 40 896 :=
  .seq (route (768,8)) (.seq (route (780,5))
    (.seq (.call (ProgramLinking.liftProgram Normalize.program registers normalizerStacks))
      (.seq (route (9,768)) clearLow)))

theorem normalizer_eval {m depth : ℕ} (hm : 0 < m) (a : Data)
    (hlow : ∀ j : Fin 896, j.val < 12 → a.stacks j = []) (ht : a.stacks 767 = [])
    (hraw : (a.stacks 768).length = HashCandidates.payloadWidth m depth)
    (hwidth : (a.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (a.stacks 780) = 3 * m) :
    ∃ n ≤ Normalize.budget m depth +
        100 * ((a.stacks 768).length + (a.stacks 780).length + 1), ∃ b,
      Eval normalizer n a b ∧ b.stacks = Function.update a.stacks 768
        (HashCandidates.normalize m depth (a.stacks 768)) := by
  have hl0 := hlow 0 (by decide)
  have hl1 := hlow 1 (by decide)
  have hl2 := hlow 2 (by decide)
  have hl3 := hlow 3 (by decide)
  have hl4 := hlow 4 (by decide)
  have hl5 := hlow 5 (by decide)
  have hl6 := hlow 6 (by decide)
  have hl7 := hlow 7 (by decide)
  have hl8 := hlow 8 (by decide)
  have hl9 := hlow 9 (by decide)
  have hl10 := hlow 10 (by decide)
  have hl11 := hlow 11 (by decide)
  let raw := a.stacks 768
  let modulus := a.stacks 780
  let canon := HashCandidates.normalize m depth raw
  let a1 := routed (768,8) a
  let a2 := routed (780,5) a1
  have he1 := route_eval (768,8) (by unfold routeValid; decide) a ht
  have he2 := route_eval (780,5) (by unfold routeValid; decide) a1
    (by simp [a1, routed, ht])
  let d := projectState registers normalizerStacks a2
  have hr : Function.Injective registers := Fin.castAdd_injective 8 32
  have hs : Function.Injective normalizerStacks := Fin.castAdd_injective 12 884
  have hd : d = Normalize.state d.regs [] modulus raw [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [normalizerStacks, a2, a1, routed, raw, modulus,
        hl0, hl1, hl2, hl3, hl4, hl6, hl7, hl9, hl10, hl11]
  obtain ⟨rf, q, hq, htq⟩ := Normalize.program_runs hm d.regs raw modulus hraw hwidth hvalue
  rw [← hd] at htq
  let out := Normalize.state rf [] modulus [] canon
  let a3 := embedState registers normalizerStacks a2 out
  have he3 : Eval (.call (ProgramLinking.liftProgram Normalize.program registers normalizerStacks))
      q a2 a3 := eval_call_from_state _ _ _ a2 hr hs htq
  have ha3 : a3.stacks = Function.update (Function.update a2.stacks 8 []) 9 canon := by
    have hout : out.stacks = Function.update (Function.update d.stacks 8 []) 9 canon := by
      funext j
      fin_cases j <;> simp [out, d, projectState, normalizerStacks, Normalize.state,
        a2, a1, routed, modulus, hl0, hl1, hl2, hl3, hl4, hl6, hl7,
        hl10, hl11]
    change Function.extend normalizerStacks out.stacks a2.stacks = _
    rw [hout, ProgramLinking.extend_update hs, ProgramLinking.extend_update hs]
    have hf : Function.extend normalizerStacks d.stacks a2.stacks = a2.stacks :=
      congrArg StructuredProgram.State.stacks (embedState_project registers normalizerStacks a2 hr hs)
    rw [hf]
    rfl
  let a4 := routed (9,768) a3
  have he4 := route_eval (9,768) (by unfold routeValid; decide) a3
    (by rw [ha3]; simp [a2, a1, routed, ht])
  have htemp : a4.stacks 767 = [] := by
    dsimp [a4, routed]
    rw [Function.update_of_ne (by decide : (767 : Fin 896) ≠ 768), ha3]
    simp [a2, a1, routed, ht]
  have he5 := BankRoutines.clear_eval (767 : Fin 896) (0 : Fin 40) 1 lowPorts
    (by decide) a4.regs a4.stacks htemp
  have hfinal : BankRoutines.clearBankStacks lowPorts a4.stacks =
      Function.update a.stacks 768 canon := by
    funext j
    by_cases hj : j ∈ lowPorts
    · have hjv := (mem_lowPorts j).mp hj
      have hj768 : j ≠ 768 := by intro he; subst j; exact (by decide : ¬ (768 : Fin 896).val < 12) hjv
      simp [BankRoutines.clearBankStacks, hj, hj768, hlow j hjv]
    · have hj5 : j ≠ 5 := by intro he; subst j; exact hj (by decide)
      have hj8 : j ≠ 8 := by intro he; subst j; exact hj (by decide)
      have hj9 : j ≠ 9 := by intro he; subst j; exact hj (by decide)
      by_cases hj768 : j = 768
      · subst j
        simp [BankRoutines.clearBankStacks, hj, a4, routed, ha3]
      · simp [BankRoutines.clearBankStacks, hj, a4, routed, ha3, a2, a1,
          hj768, hj5, hj8, hj9]
  rw [hfinal] at he5
  have hsum : (lowPorts.map (fun j => (a4.stacks j).length)).sum = modulus.length + canon.length := by
    simp [lowPorts, a4, routed, ha3, a2, a1, raw, modulus,
      hl0, hl1, hl2, hl3, hl4, hl6, hl7, hl10, hl11, Nat.add_comm]
  have hcanon : canon.length = raw.length := by
    simp only [canon, HashCandidates.normalize_length, raw, hraw]
  refine ⟨routeCost (768,8) a + (routeCost (780,5) a1 +
    (q + (routeCost (9,768) a3 + (2 * (lowPorts.map (fun j => (a4.stacks j).length)).sum +
      3 * lowPorts.length + 3)))), ?_, _, he1.seq (he2.seq (he3.seq (he4.seq he5))), rfl⟩
  have hc1 : routeCost (768,8) a = 7 * raw.length + 8 := by
    simp [routeCost, raw, hl8]
  have hc2 : routeCost (780,5) a1 = 7 * modulus.length + 8 := by
    simp [routeCost, a1, routed, modulus, hl5]
  have hc4 : routeCost (9,768) a3 = 2 * raw.length + 7 * canon.length + 8 := by
    simp [routeCost, ha3, a2, a1, routed, raw]
  rw [hc1, hc2, hc4, hsum, hcanon]
  simp only [lowPorts, List.length_cons, List.length_nil]
  change _ ≤ Normalize.budget m depth + 100 * (raw.length + modulus.length + 1)
  omega

def prepare : Cmd 40 896 := .seq loader normalizer

def budget (m depth : ℕ) : ℕ := Normalize.budget m depth +
  200 * (HashCandidates.payloadWidth m depth + HashCandidates.digitWidth m + 1)

theorem budget_polynomial (m depth : ℕ) :
    budget m depth + 1 ≤ 6200 * (depth + 1) * (HashCandidates.digitWidth m + 1) ^ 2 := by
  have hn := Normalize.budget_polynomial m depth
  have hp : HashCandidates.payloadWidth m depth + HashCandidates.digitWidth m + 1 ≤
      (depth + 1) * (HashCandidates.digitWidth m + 1) ^ 2 := by
    unfold HashCandidates.payloadWidth
    nlinarith
  unfold budget
  nlinarith

/-- The concrete preparation wrapper preserves every stack except the next
candidate payload; in particular incumbent, history, counter and parameters. -/
theorem prepare_eval {m depth : ℕ} (hm : 0 < m) (a : Data) (word : List Bool)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hcounter : a.stacks 778 = Encoding.encodeList id [word])
    (hclean : ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 → a.stacks (loaderStacks j) = [])
    (hlow : ∀ j : Fin 896, j.val < 12 → a.stacks j = []) (ht : a.stacks 767 = [])
    (hwidth : (a.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (a.stacks 780) = 3 * m) :
    ∃ n ≤ budget m depth, ∃ b, Eval prepare n a b ∧
      b.stacks = Function.update a.stacks 768
        (HashCandidates.normalize m depth word.reverse) := by
  obtain ⟨a1, he1, ha1⟩ := loader_eval a word hcounter hclean
  have hl : ∀ j : Fin 896, j.val < 12 → a1.stacks j = [] := by
    intro j hj
    have hj768 : j ≠ 768 := by intro he; subst j; exact (by decide : ¬ (768 : Fin 896).val < 12) hj
    simpa [ha1, hj768] using hlow j hj
  obtain ⟨n, hn, b, he2, hb⟩ := normalizer_eval (depth := depth) hm a1 hl
    (by simp [ha1, ht]) (by simp [ha1, hword])
    (by simpa [ha1] using hwidth) (by simpa [ha1] using hvalue)
  refine ⟨20 * word.length + 39 + n, ?_, b, he1.seq he2, ?_⟩
  · simp only [ha1, Function.update_self, List.length_reverse,
      Function.update_of_ne (by decide : (780 : Fin 896) ≠ 768), hwidth, hword] at hn ⊢
    unfold budget
    omega
  · simpa [ha1] using hb

def program := compiled prepare 778 768

theorem trace_space {m depth : ℕ} (hm : 0 < m) (a : Data) (word : List Bool) (L : ℕ)
    (hL : ∀ j, (a.stacks j).length ≤ L)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hcounter : a.stacks 778 = Encoding.encodeList id [word])
    (hclean : ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 → a.stacks (loaderStacks j) = [])
    (hlow : ∀ j : Fin 896, j.val < 12 → a.stacks j = []) (ht : a.stacks 767 = [])
    (hwidth : (a.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (a.stacks 780) = 3 * m) :
    ∃ n ≤ budget m depth + 1, ∃ b : Data,
      Trace program n (a.withPC (some program.entry)) (b.withPC none) ∧
      b.stacks = Function.update a.stacks 768
        (HashCandidates.normalize m depth word.reverse) ∧
      ∀ k c, k ≤ n → Trace program k (a.withPC (some program.entry)) c →
        ∀ j, (c.stacks j).length ≤ 896 * L + budget m depth + 1 := by
  obtain ⟨n, hn, b, he, hb⟩ := prepare_eval hm a word hword hcounter hclean hlow ht hwidth hvalue
  refine ⟨n + 1, by omega, b, compiled_halt_trace he 778 768, hb, ?_⟩
  intro k c hk hc j
  have hinit : dataBits (a.withPC (some program.entry)) ≤ 896 * L := by
    unfold dataBits stackBits
    calc
      _ ≤ ∑ _i : Fin 896, L := Finset.sum_le_sum fun i _ => hL i
      _ = _ := by simp
  have h := StructuredSpace.local_stack_bound program (steps := n + 1) hinit k c hk hc j
  omega

/-- The global call uses the frozen80-register/1220-stack ABI embedding. -/
def globalCall : Cmd 80 1220 := ABI.leafCall program

end Leaf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram
