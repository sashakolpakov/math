import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramCallback
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGraphCallback
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeCandidateProgram

/-!
# Space of the concrete sparse-code predicates

The local-code and Walsh predicates are polynomial-time bit programs. These bounds apply
to every candidate, including losing candidates, and every stack in each actual source
prefix. They are intended as the body estimates of bounded-memory enumeration; the
materialized candidate-family programs are not used here.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

theorem no_local_rejection_iff {t D d : ℕ} (Q : Fin t → Fin D → SparseCode.F3) :
    (∀ x, ¬ wordRejects Q x d) ↔ SparseCode.HasDistance Q d := by
  constructor
  · intro h x hx hx0
    by_contra hlt
    exact h x ⟨hx, hx0, Nat.lt_of_not_ge hlt⟩
  · intro h x hx
    exact Nat.not_lt_of_ge (h x hx.1 hx.2.1) hx.2.2

theorem no_graph_rejection_iff {r D : ℕ} (s : Fin D → Cayley.Cube r) (q : ℕ) :
    (∀ x, ¬ graphWordRejects s x q) ↔ WalshExistence.Good q s := by
  rw [WalshExistence.good_iff_parity_checks]
  constructor
  · intro h x hx
    by_contra hbad
    exact h x ⟨hx, hbad⟩
  · intro h x hx
    exact hx.2 (h x hx.1)

theorem field_frames_eq {p d : ℕ} [Fact p.Prime] (x : Fin d → ZMod p) :
    (CodeCandidates.fieldWords x).flatMap Encoding.frame = scalarFrames (List.ofFn x) := by
  simp [CodeCandidates.fieldWords, scalarFrames, words_eq_flatMap,
    scalarWord_eq, List.map_ofFn, Function.comp_def]

theorem pair_frames_eq {p d : ℕ} [Fact p.Prime] (xs : List (Bool × Bool))
    (x : Fin d → ZMod p) (h : xs.map CodeCandidates.digitBits = CodeCandidates.fieldWords x) :
    CodeCandidates.scalarFrames xs = scalarFrames (List.ofFn x) := by
  rw [← field_frames_eq, ← h, List.flatMap_map]
  rfl

/-- Both scans use fixed finite control and retain one encoded counter tuple. -/
abbrev ScanState := State 16 40

def graphStreamStacks : Fin 36 → Fin 40 := Fin.castAdd 4
def localStreamStacks : Fin 24 → Fin 40 := Fin.castAdd 16

def graphCounterPorts : CounterForPrograms.Ports 16 40 where
  register := ⟨Fin.castAdd 13, Fin.castAdd_injective _ _⟩
  counter := 36
  scratch := 38
  counter_ne_scratch := by decide

def localCounterPorts : CounterForPrograms.Ports 16 40 where
  register := ⟨Fin.castAdd 13, Fin.castAdd_injective _ _⟩
  counter := 24
  scratch := 26
  counter_ne_scratch := by decide

def copyConvertCommand {S : ℕ} (ternary : Bool)
    (current input payload scratch : Fin S) : Cmd 16 S :=
  .seq (SubexpSetupStorage.copyCmd current input scratch)
    (.call (ProgramLinking.liftProgram (CodeCandidateProgram.convert ternary)
      (Fin.castAdd 11) ![input, payload]))

/-- Conversion is paid for afresh at every visit. The current counter remains
available, while the temporary input is consumed and all off-port stacks survive. -/
theorem copy_convert_eval {S : ℕ} (ternary : Bool)
    (current input payload scratch : Fin S)
    (hci : current ≠ input) (hct : current ≠ scratch) (hti : scratch ≠ input)
    (hip : input ≠ payload) (xs : List (Bool × Bool)) (a : State 16 S)
    (hcurrent : a.stacks current = CodeCandidates.tupleBits xs)
    (hinput : a.stacks input = []) (hpayload : a.stacks payload = [])
    (hscratch : a.stacks scratch = []) :
    ∃ b, Eval (copyConvertCommand ternary current input payload scratch)
        (58 * xs.length + 16) a b ∧
      b.regs 4 = xs.any (CodeCandidates.invalidDigit ternary) ∧
      b.stacks input = [] ∧ b.stacks payload = (CodeCandidates.scalarFrames xs).reverse ∧
      (∀ i, i ≠ input → i ≠ payload → b.stacks i = a.stacks i) := by
  let copied := SubexpSetupStorage.copyState current input a
  have hcopy := SubexpSetupStorage.copy_eval current input scratch a hci hct hti hscratch
  have hcopied : copied.stacks input = CodeCandidates.tupleBits xs := by
    simp [copied, SubexpSetupStorage.copyState_stack, hcurrent, hinput]
  let registers : Fin 5 ↪ Fin 16 := ⟨Fin.castAdd 11, Fin.castAdd_injective _ _⟩
  let ports : Fin 2 ↪ Fin S := ⟨![input, payload], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  obtain ⟨b, hrun, hflag, hempty, hword, hframe, _⟩ :=
    CodeCandidateProgram.convert_call ternary registers ports xs copied hcopied
  refine ⟨b, ?_, hflag, hempty, ?_, ?_⟩
  · have h := hcopy.seq hrun
    rw [hcurrent, CodeCandidates.tupleBits_length] at h
    convert h using 1
    · rfl
    · omega
  · have hcopypayload : copied.stacks payload = [] :=
      (SubexpSetupStorage.copyState_frame current input payload a (Ne.symm hip)).trans hpayload
    change b.stacks payload = (CodeCandidates.scalarFrames xs).reverse ++ copied.stacks payload at hword
    simpa only [hcopypayload, List.append_nil] using hword
  · intro i hi hp
    rw [hframe i (by
      rintro ⟨j, hj⟩
      fin_cases j
      · change input = i at hj
        exact hi hj.symm
      · change payload = i at hj
        exact hp hj.symm)]
    exact SubexpSetupStorage.copyState_frame current input i a hi

/-- Invalid digits pay for copying, conversion, the branch, and full payload
cleanup. They do not change any retained stack or the rejection latch. -/
theorem invalid_conversion_eval {S : ℕ} (ternary : Bool)
    (current input payload scratch : Fin S) (accepted : Cmd 16 S)
    (hci : current ≠ input) (hct : current ≠ scratch) (hti : scratch ≠ input)
    (hip : input ≠ payload) (xs : List (Bool × Bool)) (a : State 16 S)
    (hcurrent : a.stacks current = CodeCandidates.tupleBits xs)
    (hinput : a.stacks input = []) (hpayload : a.stacks payload = [])
    (hscratch : a.stacks scratch = [])
    (hbad : xs.any (CodeCandidates.invalidDigit ternary) = true) :
    ∃ out, Eval (.seq (copyConvertCommand ternary current input payload scratch)
        (.ite 4 (SubexpSetupStorage.clearCmd payload) accepted))
        (68 * xs.length + 20) a out ∧ out.stacks = a.stacks := by
  obtain ⟨b, hconvert, hflag, hinput', hword, hframe⟩ :=
    copy_convert_eval ternary current input payload scratch hci hct hti hip xs a
      hcurrent hinput hpayload hscratch
  refine ⟨SubexpSetupStorage.clearState payload b, ?_, ?_⟩
  · have hclear := SubexpSetupStorage.clear_eval payload b
    rw [hword, List.length_reverse, CodeCandidates.scalarFrames_length] at hclear
    have h := hconvert.seq (Eval.ite_true (no := accepted) (hflag.trans hbad) hclear)
    convert h using 1; omega
  · funext i
    by_cases hp : i = payload
    · subst i
      simp [SubexpSetupStorage.clearState, hpayload]
    · by_cases hi : i = input
      · subst i
        simp [SubexpSetupStorage.clearState, hip, hinput', hinput]
      · simpa [SubexpSetupStorage.clearState, hp] using hframe i hi hp

/-- The result is a one-bit OR latch, not a retained list of check results. -/
def latchReject (port : Fin 40) : Cmd 16 40 :=
  .seq (.base (.atom (.pop port 13 14))) <|
  .seq (.base (.atom (.bor 13 13 15))) (.base (.atom (.push port 13)))

def graphStreamBody : Cmd 16 40 :=
  .seq (copyConvertCommand false 36 39 34 35) <|
  .ite 4 (SubexpSetupStorage.clearCmd 34)
    (.seq (.call (ProgramLinking.liftProgram graphCallbackProgram id graphStreamStacks))
      (latchReject 37))

def localStreamBody : Cmd 16 40 :=
  .seq (copyConvertCommand true 24 27 22 23) <|
  .ite 4 (SubexpSetupStorage.clearCmd 22)
    (.seq (.call (ProgramLinking.liftProgram callbackProgram id localStreamStacks))
      (latchReject 25))

def graphStreamCommand : Cmd 16 40 :=
  ExecCNFTupleEnumeration.enumerate graphCounterPorts graphStreamBody

def localStreamCommand : Cmd 16 40 :=
  ExecCNFTupleEnumeration.enumerate localCounterPorts localStreamBody

def graphStreamProgram := compiled graphStreamCommand 36 37
def localStreamProgram := compiled localStreamCommand 24 25

def graphStreamBudget (D r qlen Dlen : ℕ) : ℕ :=
  4 ^ r * (graphCallbackBudget D r qlen Dlen + 110 * r + 36) + 3

def localStreamBudget (t D d : ℕ) : ℕ :=
  4 ^ D * (callbackBudget t D d + 110 * D + 36) + 3

/-- Invalid two-bit ternary digits cost at most a square of the old complete
matrix-and-word domain. This power is independent of the input. -/
theorem local_attempts_le_square (t D : ℕ) :
    4 ^ (t * D) * 4 ^ D ≤ (3 ^ (t * D) * 3 ^ D) ^ 2 := by
  rw [← pow_add, ← pow_add]
  calc
    4 ^ (t * D + D) ≤ 9 ^ (t * D + D) := Nat.pow_le_pow_left (by decide) _
    _ = (3 ^ (t * D + D)) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm (t * D + D) 2, pow_mul]
      norm_num

/-- The graph's invalid high-bit words are also charged by a fixed square. -/
theorem graph_attempts_eq_square (D r : ℕ) :
    4 ^ (D * r) * 4 ^ r = (2 ^ (D * r) * 2 ^ r) ^ 2 := by
  rw [← pow_add, ← pow_add, ← pow_mul, Nat.mul_comm (D * r + r) 2, pow_mul]
  norm_num

theorem latchReject_eval (port : Fin 40) (a : ScanState) (b : Bool)
    (hport : a.stacks port = [b]) :
    ∃ out : ScanState, Eval (latchReject port) 3 a out ∧
      out.stacks port = [b || a.regs 15] ∧
      (∀ i, i ≠ port → out.stacks i = a.stacks i) := by
  let popped := (StructuredProgram.Atom.pop port 13 14).eval a
  let joined := (StructuredProgram.Atom.bor 13 13 15).eval popped
  let out := (StructuredProgram.Atom.push port 13).eval joined
  refine ⟨out, ?_, ?_, ?_⟩
  · exact (Eval.base (.atom _ a)).seq
      ((Eval.base (.atom _ popped)).seq (Eval.base (.atom _ joined)))
  · simp [out, joined, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,
      execInstr, readRegs, hport]
  · intro i hi
    simp [out, joined, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, hi]

private theorem fold_rejection_latch (ranks : List ℕ) (reject : ℕ → Bool) (b : Bool) :
    ranks.foldl (fun word rank => [word.headD false || reject rank]) [b] =
      [b || ranks.any reject] := by
  induction ranks generalizing b with
  | nil => simp
  | cons rank ranks ih =>
      change ranks.foldl (fun word rank => [word.headD false || reject rank])
        [b || reject rank] = [b || (reject rank || ranks.any reject)]
      rw [ih, Bool.or_assoc]

/-- A semantic visit log describes the actual latch updates. The log is proof
data only; the machine retains one Boolean and the current counter word. -/
theorem visits_rejection_latch {R S : ℕ} {p : CounterForPrograms.Ports R S}
    {body : Cmd R S} {shape ranks : List ℕ} {steps : ℕ} {a out : State R S}
    (hvis : ExecCNFTupleEnumeration.Visits p body shape ranks steps a out)
    (port : Fin S) (hc : port ≠ p.counter) (hs : port ≠ p.scratch)
    (reject : ℕ → Bool) (b : Bool) (hstart : a.stacks port = [b])
    (hbody : ∀ words a e nb, words.map List.length = shape →
      a.stacks p.counter = Encoding.encodeList id words → Eval body nb a e →
      e.stacks port = [(a.stacks port).headD false ||
        reject (CounterPrograms.value words.flatten)]) :
    out.stacks port = [b || ranks.any reject] := by
  rw [hvis.stack_fold port hc hs
    (fun word rank => [word.headD false || reject rank]) hbody, hstart]
  exact fold_rejection_latch ranks reject b

/-- A valid streamed character is checked by the original bit arithmetic. Only
the one-bit rejection latch changes; this includes every off-port caller stack. -/
theorem graph_stream_body_valid {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (xs : List (Bool × Bool))
    (hfields : xs.map CodeCandidates.digitBits = CodeCandidates.fieldWords x)
    (hvalid : xs.any (CodeCandidates.invalidDigit false) = false)
    (a : ScanState) (b : Bool)
    (he : GraphWorkEmpty (projectState id graphStreamStacks a))
    (hm : a.stacks 29 = matrixFrames s) (ht : a.stacks 30 = List.replicate D true)
    (hq : a.stacks 31 = qbits) (hD : a.stacks 32 = Dbits)
    (hpayload : a.stacks 34 = []) (htmp : a.stacks 35 = [])
    (hcounter : a.stacks 36 = CodeCandidates.tupleBits xs)
    (hlatch : a.stacks 37 = [b]) (hcopy : a.stacks 39 = []) :
    ∃ steps out, steps ≤ graphCallbackBudget D r qbits.length Dbits.length + 68 * r + 24 ∧
      Eval graphStreamBody steps a out ∧
      out.stacks = Function.update a.stacks 37 [b || decide (graphWordRejects s x q)] := by
  have hlen : xs.length = r := by simpa using congrArg List.length hfields
  obtain ⟨c, hconvert, hflag, hcopy', hword, hcframe⟩ :=
    copy_convert_eval false 36 39 34 35 (by decide) (by decide) (by decide) (by decide)
      xs a hcounter hcopy hpayload htmp
  have hlow (i : Fin 34) : c.stacks ⟨i.val, by omega⟩ = a.stacks ⟨i.val, by omega⟩ := by
    apply hcframe <;> intro h <;> have hv := congrArg Fin.val h <;>
      simp only at hv <;> omega
  have hwork : GraphWorkEmpty (projectState id graphStreamStacks c) := by
    intro i
    exact (hlow ⟨i.val, by omega⟩).trans (he i)
  have h35 : c.stacks 35 = [] := (hcframe 35 (by decide) (by decide)).trans htmp
  have h34 : c.stacks 34 = (scalarFrames (List.ofFn x)).reverse := by
    rw [hword, pair_frames_eq xs x hfields]
  obtain ⟨n, small, hn, hrun, hworkout, hreject, _, _, h34out, hframe⟩ :=
    graphWordCallback_eval s x q qbits Dbits hqv hDv
      (projectState id graphStreamStacks c) hwork
      ((hlow 29).trans hm) ((hlow 30).trans ht) ((hlow 31).trans hq)
      ((hlow 32).trans hD) h35 h34
  let middle := embedState id graphStreamStacks c small
  have hcall := eval_call_from_state graphCallbackProgram id graphStreamStacks c
    Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace hrun 34 34)
  have hmid (i : Fin 36) : middle.stacks (graphStreamStacks i) = small.stacks i :=
    embedState_stack id graphStreamStacks c small (Fin.castAdd_injective _ _) i
  have hmidreg : middle.regs 15 = decide (graphWordRejects s x q) :=
    (embedState_register id graphStreamStacks c small Function.injective_id 15).trans hreject
  have hstacks : middle.stacks = a.stacks := by
    funext i
    by_cases hi : i.val < 29
    · let j : Fin 29 := ⟨i.val, hi⟩
      have hij : graphStreamStacks (graphWordStacks j) = i := Fin.ext rfl
      rw [← hij, hmid, hworkout j]
      exact (he j).symm
    · by_cases h34i : i = 34
      · subst i
        exact (hmid 34).trans (h34out.trans hpayload.symm)
      · by_cases hi36 : i.val < 36
        · let j : Fin 36 := ⟨i.val, hi36⟩
          have hij : graphStreamStacks j = i := Fin.ext rfl
          have hj34 : j ≠ 34 := by
            intro h
            apply h34i
            exact Fin.ext (by simpa [j] using congrArg Fin.val h)
          have h39i : i ≠ 39 := by
            intro h
            have hv := congrArg Fin.val h
            omega
          rw [← hij, hmid]
          exact (hframe j (by change 29 ≤ i.val; omega) hj34).trans (hcframe i h39i h34i)
        · have houter : middle.stacks i = c.stacks i := by
            apply embedState_stack_frame
            rintro ⟨j, hj⟩
            have hv := congrArg Fin.val hj
            change j.val = i.val at hv
            omega
          rw [houter]
          by_cases h39i : i = 39
          · subst i
            exact hcopy'.trans hcopy.symm
          · exact hcframe i h39i h34i
  obtain ⟨out, hor, hout, houtframe⟩ :=
    latchReject_eval 37 middle b ((congrFun hstacks 37).trans hlatch)
  refine ⟨(58 * xs.length + 16) + (n + 1 + 3 + 1), out, ?_, ?_, ?_⟩
  · rw [hlen]
    omega
  · exact hconvert.seq (Eval.ite_false (hflag.trans hvalid) (hcall.seq hor))
  · funext i
    by_cases hi : i = 37
    · subst i
      simpa [hmidreg] using hout
    · simpa [Function.update_of_ne hi] using (houtframe i hi).trans (congrFun hstacks i)

/-- A valid streamed local-code word is checked by the original bit arithmetic. Only
the one-bit rejection latch changes; this includes every off-port caller stack. -/
theorem local_stream_body_valid {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ)
    (xs : List (Bool × Bool))
    (hfields : xs.map CodeCandidates.digitBits = CodeCandidates.fieldWords x)
    (hvalid : xs.any (CodeCandidates.invalidDigit true) = false)
    (a : ScanState) (b : Bool)
    (he : WorkEmpty (projectState id localStreamStacks a))
    (hm : a.stacks 18 = matrixFrames Q) (ht : a.stacks 19 = List.replicate t true)
    (hd : a.stacks 20 = List.replicate d true)
    (hpayload : a.stacks 22 = []) (htmp : a.stacks 23 = [])
    (hcounter : a.stacks 24 = CodeCandidates.tupleBits xs)
    (hlatch : a.stacks 25 = [b]) (hcopy : a.stacks 27 = []) :
    ∃ steps out, steps ≤ callbackBudget t D d + 68 * D + 24 ∧
      Eval localStreamBody steps a out ∧
      out.stacks = Function.update a.stacks 25 [b || decide (wordRejects Q x d)] := by
  have hlen : xs.length = D := by simpa using congrArg List.length hfields
  obtain ⟨c, hconvert, hflag, hcopy', hword, hcframe⟩ :=
    copy_convert_eval true 24 27 22 23 (by decide) (by decide) (by decide) (by decide)
      xs a hcounter hcopy hpayload htmp
  have hlow (i : Fin 22) : c.stacks ⟨i.val, by omega⟩ = a.stacks ⟨i.val, by omega⟩ := by
    apply hcframe <;> intro h <;> have hv := congrArg Fin.val h <;>
      simp only at hv <;> omega
  have hwork : WorkEmpty (projectState id localStreamStacks c) := by
    intro i
    exact (hlow ⟨i.val, by omega⟩).trans (he i)
  have h35 : c.stacks 23 = [] := (hcframe 23 (by decide) (by decide)).trans htmp
  have h34 : c.stacks 22 = (scalarFrames (List.ofFn x)).reverse := by
    rw [hword, pair_frames_eq xs x hfields]
  obtain ⟨n, small, hn, hrun, hworkout, hreject, _, _, h34out, hframe⟩ :=
    wordCallback_eval Q x d
      (projectState id localStreamStacks c) hwork
      ((hlow 18).trans hm) ((hlow 19).trans ht) ((hlow 20).trans hd) h35 h34
  let middle := embedState id localStreamStacks c small
  have hcall := eval_call_from_state callbackProgram id localStreamStacks c
    Function.injective_id (Fin.castAdd_injective _ _) (compiled_halt_trace hrun 22 22)
  have hmid (i : Fin 24) : middle.stacks (localStreamStacks i) = small.stacks i :=
    embedState_stack id localStreamStacks c small (Fin.castAdd_injective _ _) i
  have hmidreg : middle.regs 15 = decide (wordRejects Q x d) :=
    (embedState_register id localStreamStacks c small Function.injective_id 15).trans hreject
  have hstacks : middle.stacks = a.stacks := by
    funext i
    by_cases hi : i.val < 18
    · let j : Fin 18 := ⟨i.val, hi⟩
      have hij : localStreamStacks (wordStacks j) = i := Fin.ext rfl
      rw [← hij, hmid, hworkout j]
      exact (he j).symm
    · by_cases h34i : i = 22
      · subst i
        exact (hmid 22).trans (h34out.trans hpayload.symm)
      · by_cases hi36 : i.val < 24
        · let j : Fin 24 := ⟨i.val, hi36⟩
          have hij : localStreamStacks j = i := Fin.ext rfl
          have hj34 : j ≠ 22 := by
            intro h
            apply h34i
            exact Fin.ext (by simpa [j] using congrArg Fin.val h)
          have h39i : i ≠ 27 := by
            intro h
            have hv := congrArg Fin.val h
            omega
          rw [← hij, hmid]
          exact (hframe j (by change 18 ≤ i.val; omega) hj34).trans (hcframe i h39i h34i)
        · have houter : middle.stacks i = c.stacks i := by
            apply embedState_stack_frame
            rintro ⟨j, hj⟩
            have hv := congrArg Fin.val hj
            change j.val = i.val at hv
            omega
          rw [houter]
          by_cases h39i : i = 27
          · subst i
            exact hcopy'.trans hcopy.symm
          · exact hcframe i h39i h34i
  obtain ⟨out, hor, hout, houtframe⟩ :=
    latchReject_eval 25 middle b ((congrFun hstacks 25).trans hlatch)
  refine ⟨(58 * xs.length + 16) + (n + 1 + 3 + 1), out, ?_, ?_, ?_⟩
  · rw [hlen]
    omega
  · exact hconvert.seq (Eval.ite_false (hflag.trans hvalid) (hcall.seq hor))
  · funext i
    by_cases hi : i = 25
    · subst i
      simpa [hmidreg] using hout
    · simpa [Function.update_of_ne hi] using (houtframe i hi).trans (congrFun hstacks i)

/-- This includes the caller's retained word on stack21; no stack is omitted. -/
theorem local_input_bound {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ) (a : SearchState)
    (he : WorkEmpty a) (hm : a.stacks 18 = matrixFrames Q)
    (ht : a.stacks 19 = List.replicate t true)
    (hd : a.stacks 20 = List.replicate d true) (htmp : a.stacks 23 = [])
    (hx : a.stacks 22 = (scalarFrames (List.ofFn x)).reverse) (i : Fin 24) :
    (a.stacks i).length ≤ (a.stacks 21).length + 5 * (t * D) + t + d + 5 * D := by
  by_cases hi : i.val < 18
  · let j : Fin 18 := ⟨i.val, hi⟩
    have hj : wordStacks j = i := Fin.ext rfl
    rw [← hj, he j]
    exact Nat.zero_le _
  · fin_cases i <;>
      simp_all [matrixFrames_ternary_length, scalarFrames_ternary_length] <;> omega

/-- Walsh inputs include the full retained caller word on stack33. -/
theorem graph_input_bound {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (qbits Dbits : List Bool) (a : GraphSearchState)
    (he : GraphWorkEmpty a) (hm : a.stacks 29 = matrixFrames s)
    (ht : a.stacks 30 = List.replicate D true)
    (hq : a.stacks 31 = qbits) (hD : a.stacks 32 = Dbits) (htmp : a.stacks 35 = [])
    (hx : a.stacks 34 = (scalarFrames (List.ofFn x)).reverse) (i : Fin 36) :
    (a.stacks i).length ≤
      (a.stacks 33).length + 5 * (D * r) + D + qbits.length + Dbits.length + 5 * r := by
  by_cases hi : i.val < 29
  · let j : Fin 29 := ⟨i.val, hi⟩
    have hj : graphWordStacks j = i := Fin.ext rfl
    rw [← hj, he j]
    exact Nat.zero_le _
  · fin_cases i <;>
      simp_all [matrixFrames_binary_length, scalarFrames_binary_length] <;> omega

/-- The local predicate has a fixed polynomial budget, independently of acceptance. -/
theorem local_budget (t D d : ℕ) :
    callbackBudget t D d =
      4000766 * (t * D) + 3595 * t + 713 * D + 43 * d + 1148 := by
  simp only [callbackBudget, wordBudget, wordInputSpan, wordTailBudget,
    OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.matrixBudget, OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.rowBudget,
    OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgram.termBudget]
  ring

/-- All scalar comparison and cleanup work is included in the Walsh predicate budget. -/
theorem graph_budget (D r qlen Dlen : ℕ) :
    graphCallbackBudget D r qlen Dlen =
      6379582 * (D * r) + 5729 * D + 895 * r + 65 * qlen + 65 * Dlen + 1588 +
        41300 * (2 * (qlen + Dlen + D) + 4) ^ 2 := by
  simp only [graphCallbackBudget, graphWordBudget, graphInputSpan, graphCountsBudget,
    OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.matrixBudget, OAI.Algorithms.SubexponentialSAT.Subexp.MatrixVectorProgram.rowBudget,
    OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgram.termBudget]
  ring

/-- The actual complete local-word check has the same all-stack prefix estimate on both
accepting and rejecting words. The initial bound includes the suspended caller's stack21.
The final halt is included in both time and space. -/
theorem local_check_runs_space {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (x : Fin D → SparseCode.F3) (d : ℕ) (a : SearchState) (initialBound : ℕ)
    (he : WorkEmpty a) (hm : a.stacks 18 = matrixFrames Q)
    (ht : a.stacks 19 = List.replicate t true)
    (hd : a.stacks 20 = List.replicate d true) (htmp : a.stacks 23 = [])
    (hx : a.stacks 22 = (scalarFrames (List.ofFn x)).reverse)
    (ha : ∀ i, (a.stacks i).length ≤ initialBound) :
    ∃ (steps : ℕ) (out : SearchState),
      steps ≤ callbackBudget t D d + 1 ∧
      Trace callbackProgram steps (a.withPC (some callbackProgram.entry))
        (out.withPC none) ∧
      WorkEmpty out ∧ out.regs 15 = decide (wordRejects Q x d) ∧
      out.regs 13 = a.regs 13 ∧ out.regs 14 = a.regs 14 ∧ out.stacks 22 = [] ∧
      (∀ i : Fin 24, 18 ≤ i.val → i ≠ 22 → out.stacks i = a.stacks i) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace callbackProgram prefixSteps (a.withPC (some callbackProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ initialBound + callbackBudget t D d + 1) := by
  obtain ⟨steps, out, hn, hrun, hwork, hflag, h13, h14, h22, hframe⟩ :=
    wordCallback_eval Q x d a he hm ht hd htmp hx
  refine ⟨steps + 1, out, by omega, compiled_halt_trace hrun 22 22,
    hwork, hflag, h13, h14, h22, hframe, ?_⟩
  intro prefixSteps intermediate hle hprefix i
  have hgrowth := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le hprefix i
  have hi := ha i
  change (intermediate.stacks i).length ≤ (a.stacks i).length + prefixSteps at hgrowth
  omega

/-- One actual Walsh-character check, with all persistent inputs, scratch, and the caller
frame on stack33 included at every source prefix. The retained matrix need not be good. -/
theorem graph_check_runs_space {D r : ℕ} (s : Fin D → Cayley.Cube r)
    (x : Cayley.Cube r) (q : ℕ) (qbits Dbits : List Bool)
    (hqv : BinaryArithmetic.toNat qbits = q) (hDv : BinaryArithmetic.toNat Dbits = D)
    (a : GraphSearchState) (initialBound : ℕ)
    (he : GraphWorkEmpty a) (hm : a.stacks 29 = matrixFrames s)
    (ht : a.stacks 30 = List.replicate D true)
    (hq : a.stacks 31 = qbits) (hD : a.stacks 32 = Dbits) (htmp : a.stacks 35 = [])
    (hx : a.stacks 34 = (scalarFrames (List.ofFn x)).reverse)
    (ha : ∀ i, (a.stacks i).length ≤ initialBound) :
    ∃ (steps : ℕ) (out : GraphSearchState),
      steps ≤ graphCallbackBudget D r qbits.length Dbits.length + 1 ∧
      Trace graphCallbackProgram steps (a.withPC (some graphCallbackProgram.entry))
        (out.withPC none) ∧
      GraphWorkEmpty out ∧ out.regs 15 = decide (graphWordRejects s x q) ∧
      out.regs 13 = a.regs 13 ∧ out.regs 14 = a.regs 14 ∧ out.stacks 34 = [] ∧
      (∀ i : Fin 36, 29 ≤ i.val → i ≠ 34 → out.stacks i = a.stacks i) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace graphCallbackProgram prefixSteps
          (a.withPC (some graphCallbackProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          initialBound + graphCallbackBudget D r qbits.length Dbits.length + 1) := by
  obtain ⟨steps, out, hn, hrun, hwork, hflag, h13, h14, h34, hframe⟩ :=
    graphWordCallback_eval s x q qbits Dbits hqv hDv a he hm ht hq hD htmp hx
  refine ⟨steps + 1, out, by omega, compiled_halt_trace hrun 34 34,
    hwork, hflag, h13, h14, h34, hframe, ?_⟩
  intro prefixSteps intermediate hle hprefix i
  have hgrowth := OAI.Algorithms.SubexponentialSAT.Subexp.SequentialProgram.trace_stack_length_le hprefix i
  have hi := ha i
  change (intermediate.stacks i).length ≤ (a.stacks i).length + prefixSteps at hgrowth
  omega

/-- Matrix scalar order agrees with the original row-major matrix encoding.
The converter therefore stages one actual matrix without recoding a family. -/
theorem pair_matrix_frames_eq {p rows cols : ℕ} [Fact p.Prime]
    (xs : List (Bool × Bool)) (M : Fin rows → Fin cols → ZMod p)
    (h : xs.map CodeCandidates.digitBits = CodeCandidates.matrixWords M) :
    CodeCandidates.scalarFrames xs = matrixFrames M := by
  calc
    CodeCandidates.scalarFrames xs = scalarFrames (List.ofFn (flattenMatrix M)) :=
      pair_frames_eq xs (flattenMatrix M) h
    _ = framedMatrix M := (framedVector_eq_scalarFrames (flattenMatrix M)).symm
    _ = matrixFrames M := framedMatrix_eq_matrixFrames M

/-- Staging a current matrix only clears the old matrix and reverses the
converted payload. No list of all test words is copied. -/
def installMatrix {S : ℕ} (payload matrix : Fin S) : Cmd 16 S :=
  .seq (SubexpSetupStorage.clearCmd matrix)
    (.call (StackRoutines.transferProgram payload matrix 0 1))

theorem installMatrix_eval {S : ℕ} (payload matrix : Fin S) (hpm : payload ≠ matrix)
    (word : List Bool) (a : State 16 S) (hp : a.stacks payload = word.reverse) :
    ∃ out, Eval (installMatrix payload matrix)
        (2 * (a.stacks matrix).length + 3 * word.length + 6) a out ∧
      out.stacks payload = [] ∧ out.stacks matrix = word ∧
      (∀ i, i ≠ payload → i ≠ matrix → out.stacks i = a.stacks i) := by
  let cleared := SubexpSetupStorage.clearState matrix a
  let out := SubexpScanPrimitives.afterTransfer cleared payload matrix 0 1
  have hc := SubexpSetupStorage.clear_eval matrix a
  have ht := SubexpScanPrimitives.transfer_eval cleared payload matrix 0 1 hpm (by decide)
  have hpayload : cleared.stacks payload = word.reverse := by
    simpa [cleared, SubexpSetupStorage.clearState, hpm] using hp
  refine ⟨out, ?_, ?_, ?_, ?_⟩
  · have he := hc.seq ht
    rw [hpayload, List.length_reverse] at he
    convert he using 1
    · rfl
    · omega
  · simp [out, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, hpm]
  · simp [out, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks, hpm,
      cleared, SubexpSetupStorage.clearState, hp]
  · intro i hi hj
    simp [out, SubexpScanPrimitives.afterTransfer, StackRoutines.transferStacks,
      cleared, SubexpSetupStorage.clearState, hi, hj]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
