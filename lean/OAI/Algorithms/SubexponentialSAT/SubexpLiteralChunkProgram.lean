import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpClauseRowProgram
import OAI.Algorithms.SubexponentialSAT.ModularQuotientLift
import OAI.Algorithms.SubexponentialSAT.CounterConversions
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# Actual literal-index to chunk-index conversion

The input is one reversed canonical unary literal field and a binary chunk
width. The fixed program decodes the variable index, counts it into binary,
divides by the chunk width, and constructs the reversed canonical chunk field.
-/

namespace SubexponentialSAT.SubexpLiteralChunkProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 8 19

def tapes (ell unary binary remainder quotient payload encoded : List Bool) : Fin 19 → List Bool :=
  ![remainder, [], unary, [], binary, [], [], quotient, [], payload, encoded,
    [], [], [], [], [], [], [], ell]

def data (regs : Fin 8 → Bool) (ell unary binary remainder quotient payload encoded : List Bool) : Data :=
  ⟨regs, tapes ell unary binary remainder quotient payload encoded⟩

private theorem tapes_eq (ell unary binary remainder quotient payload encoded : List Bool) :
    tapes ell unary binary remainder quotient payload encoded = fun i =>
      if i = 0 then remainder else if i = 2 then unary else if i = 4 then binary
      else if i = 7 then quotient else if i = 9 then payload else if i = 10 then encoded
      else if i = 18 then ell else [] := by
  funext i; fin_cases i <;> rfl

private theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

private theorem embed_restricted {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack) (d : State R S) :
    embedState register stack d ⟨d.regs ∘ register, d.stacks ∘ stack⟩ = d := by
  apply embedState_eq_of_ports _ _ _ _ _ hr hs
  · intro i; rfl
  · intro i hi; rfl
  · intro i; rfl
  · intro i hi; rfl

private theorem embed_stacks {r s : ℕ} (register : Fin r → Fin 8) (stack : Fin s → Fin 19)
    (hs : Function.Injective stack) (frame : Data) (source : State r s)
    (target : Fin 19 → List Bool)
    (hp : ∀ i, target (stack i) = source.stacks i)
    (hf : ∀ i, (¬ ∃ j, stack j = i) → target i = frame.stacks i) :
    embedState register stack frame source =
      (⟨(embedState register stack frame source).regs, target⟩ : Data) := by
  apply state_ext
  · rfl
  ·
    funext i
    by_cases hi : ∃ j, stack j = i
    · obtain ⟨j, rfl⟩ := hi
      exact (embedState_stack register stack frame source hs j).trans (hp j).symm
    · exact (embedState_stack_frame register stack frame source i hi).trans (hf i hi).symm

def decodeRegisters : Fin 4 → Fin 8 := Fin.castAdd 4
def decodeStacks : Fin 10 → Fin 19 := Fin.castAdd 9

theorem decodeRegisters_injective : Function.Injective decodeRegisters := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)
theorem decodeStacks_injective : Function.Injective decodeStacks := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 19 => x.val) h)

abbrev decode : Cmd 8 19 := .call (ProgramLinking.liftProgram
  SubexpClauseRowProgram.LiteralDecoder.program decodeRegisters decodeStacks)

theorem decode_eval (regs : Fin 8 → Bool) (ell : List Bool) (v : ℕ) (sign : Bool) :
    ∃ rf, Eval decode (9 * v + 4 * (if sign then 1 else 0) + 5)
      (data regs ell [] [] [] []
        (Encoding.encodeNat (2 * v + if sign then 1 else 0)).reverse [])
      (data rf ell (List.replicate v true) [] [] [] [] []) := by
  let d := data regs ell [] [] [] []
    (Encoding.encodeNat (2 * v + if sign then 1 else 0)).reverse []
  let a := SubexpClauseRowProgram.data (regs 0) (regs 1) (regs 2) (regs 3)
    [] [] [] [] [] (Encoding.encodeNat (2 * v + if sign then 1 else 0)).reverse
  let b := SubexpClauseRowProgram.data false false sign (regs 3)
    [] [] (List.replicate v true) [] [] []
  have ha : a = ⟨d.regs ∘ decodeRegisters, d.stacks ∘ decodeStacks⟩ := by
    apply state_ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  have ht := SubexpClauseRowProgram.LiteralDecoder.trace v sign (regs 0) (regs 1)
    (regs 2) (regs 3) [] [] [] [] []
  simp only [List.append_nil] at ht
  have h := eval_call_lifted SubexpClauseRowProgram.LiteralDecoder.program
    decodeRegisters decodeStacks d decodeRegisters_injective decodeStacks_injective ht
  change Eval decode _ (embedState _ _ d a) (embedState _ _ d b) at h
  rw [ha, embed_restricted _ _ decodeRegisters_injective decodeStacks_injective] at h
  have hb := embed_stacks decodeRegisters decodeStacks decodeStacks_injective d b
    (tapes ell (List.replicate v true) [] [] [] [] [])
    (by intro i; fin_cases i <;> rfl)
    (by
      intro i hi
      have h2 : i ≠ 2 := fun h => hi ⟨2, by simpa [decodeStacks] using h.symm⟩
      have h9 : i ≠ 9 := fun h => hi ⟨9, by simpa [decodeStacks] using h.symm⟩
      simp only [d, data, tapes_eq, h2, h9, ite_false])
  rw [hb] at h
  exact ⟨_, h⟩

def lengthRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def lengthStacks : Fin 3 → Fin 19 := ![2, 4, 5]

theorem lengthRegisters_injective : Function.Injective lengthRegisters := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 8 => x.val) h)
theorem lengthStacks_injective : Function.Injective lengthStacks := by decide

abbrev count : Cmd 8 19 := .seq (.base (.atom (.set 2 false)))
  (.call (ProgramLinking.liftProgram CounterPrograms.lengthProgram lengthRegisters lengthStacks))

theorem count_eval (regs : Fin 8 → Bool) (ell unary : List Bool) :
    ∃ t ≤ unary.length * (8 * unary.length + 10) + 4,
      ∃ rf binary, Eval count t (data regs ell unary [] [] [] [] [])
        (data rf ell [] binary [] [] [] []) ∧
        BinaryArithmetic.toNat binary = unary.length ∧ binary.length ≤ unary.length := by
  let d := data (Function.update regs 2 false) ell unary [] [] [] [] []
  have hr : Eval (.base (.atom (.set 2 false))) 1
      (data regs ell unary [] [] [] [] []) d := .base (.atom _ _)
  obtain ⟨binary, hv, hl, t, ht, htrace⟩ :=
    CounterPrograms.length_correct_from (regs 0) (regs 1) unary
  let a : State 3 3 := ⟨CounterPrograms.counterRegs (regs 0) (regs 1) false,
    CounterPrograms.lengthStacks unary [] []⟩
  let b : State 3 3 := ⟨fun _ => false, fun j => if j = 1 then binary else []⟩
  have ha : a = ⟨d.regs ∘ lengthRegisters, d.stacks ∘ lengthStacks⟩ := by
    apply state_ext
    · funext i; fin_cases i <;> simp [a, d, data, lengthRegisters, CounterPrograms.counterRegs]
    · funext i; fin_cases i <;> rfl
  change Trace CounterPrograms.lengthProgram t
    (a.withPC (some CounterPrograms.lengthProgram.entry)) (b.withPC none) at htrace
  have h := eval_call_lifted CounterPrograms.lengthProgram lengthRegisters lengthStacks d
    lengthRegisters_injective lengthStacks_injective htrace
  rw [ha, embed_restricted _ _ lengthRegisters_injective lengthStacks_injective] at h
  have hb := embed_stacks lengthRegisters lengthStacks lengthStacks_injective d b
    (tapes ell [] binary [] [] [] [])
    (by intro i; fin_cases i <;> rfl)
    (by
      intro i hi
      have h2 : i ≠ 2 := fun h => hi ⟨0, by simpa [lengthStacks] using h.symm⟩
      have h4 : i ≠ 4 := fun h => hi ⟨1, by simpa [lengthStacks] using h.symm⟩
      simp only [d, data, tapes_eq, h2, h4, ite_false])
  rw [hb] at h
  exact ⟨1 + t, by omega, _, binary, hr.seq h,
    (CounterPrograms.value_eq_toNat binary).symm.trans hv, hl⟩

def divisionPorts : Fin 8 ↪ Fin 19 := ⟨![0, 1, 2, 3, 5, 18, 4, 7], by decide⟩
abbrev divide : Cmd 8 19 := .call (ModularQuotientLift.programAt divisionPorts)

theorem divide_eval (regs : Fin 8 → Bool) (ell binary : List Bool) :
    ∃ t ≤ 100 * (ell.length + binary.length + 1) ^ 2, ∃ rf,
      Eval divide t (data regs ell [] binary [] [] [] [])
        (data rf ell [] [] (ModularQuotientArithmetic.divide ell binary).2
          (ModularQuotientArithmetic.divide ell binary).1 [] []) := by
  obtain ⟨t, ht, rf, h⟩ := ModularQuotientLift.programAt_eval divisionPorts ell binary regs
    (tapes ell [] binary [] [] [] []) rfl rfl rfl rfl rfl rfl rfl rfl
  have he : ModularQuotientLift.quotientStacksAt divisionPorts
      (ModularQuotientArithmetic.divide ell binary).2
      (ModularQuotientArithmetic.divide ell binary).1 (tapes ell [] binary [] [] [] []) =
      tapes ell [] [] (ModularQuotientArithmetic.divide ell binary).2
        (ModularQuotientArithmetic.divide ell binary).1 [] [] := by
    funext i; fin_cases i <;> simp [ModularQuotientLift.quotientStacksAt, divisionPorts, tapes]
  rw [he] at h
  exact ⟨t, ht, rf, h⟩

def conversionRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def conversionStacks : Fin 3 → Fin 19 := ![7, 10, 8]

theorem conversionRegisters_injective : Function.Injective conversionRegisters :=
  lengthRegisters_injective
theorem conversionStacks_injective : Function.Injective conversionStacks := by decide

abbrev encode : Cmd 8 19 := .call (ProgramLinking.liftProgram
  CounterConversions.encodeNatProgram conversionRegisters conversionStacks)

theorem encode_eval (regs : Fin 8 → Bool) (ell remainder quotient : List Bool) :
    ∃ t ≤ CounterConversions.runtimeBound quotient, ∃ rf,
      Eval encode t (data regs ell [] [] remainder quotient [] [])
        (data rf ell [] [] remainder [] []
          (Encoding.encodeNat (BinaryArithmetic.toNat quotient))) := by
  let d := data regs ell [] [] remainder quotient [] []
  let a := CounterConversions.state (regs ∘ conversionRegisters) quotient []
  let b := CounterConversions.state CounterConversions.zeroRegs []
    (Encoding.encodeNat (CounterPrograms.value quotient))
  have ha : a = ⟨d.regs ∘ conversionRegisters, d.stacks ∘ conversionStacks⟩ := by
    apply state_ext
    · rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨t, ht, htrace⟩ := CounterConversions.encodeNat_runs (regs ∘ conversionRegisters) quotient
  have h := eval_call_lifted CounterConversions.encodeNatProgram conversionRegisters conversionStacks d
    conversionRegisters_injective conversionStacks_injective htrace
  change Eval encode t (embedState _ _ d a) (embedState _ _ d b) at h
  rw [ha, embed_restricted _ _ conversionRegisters_injective conversionStacks_injective] at h
  have hb := embed_stacks conversionRegisters conversionStacks conversionStacks_injective d b
    (tapes ell [] [] remainder [] [] (Encoding.encodeNat (CounterPrograms.value quotient)))
    (by intro i; fin_cases i <;> rfl)
    (by
      intro i hi
      have h7 : i ≠ 7 := fun h => hi ⟨0, by simpa [conversionStacks] using h.symm⟩
      have h10 : i ≠ 10 := fun h => hi ⟨1, by simpa [conversionStacks] using h.symm⟩
      simp only [d, data, tapes_eq, h7, h10, ite_false])
  rw [hb] at h
  rw [CounterPrograms.value_eq_toNat] at h
  exact ⟨t, ht, _, h⟩


abbrev clearRemainder : Cmd 8 19 := .call (clearProgram 0 0 1)

theorem clearRemainder_eval (regs : Fin 8 → Bool) (ell remainder encoded : List Bool) :
    Eval clearRemainder (2 * remainder.length + 3)
      (data regs ell [] [] remainder [] [] encoded)
      (data (readRegs regs 0 1 none) ell [] [] [] [] [] encoded) := by
  have h := ListRegisterProgram.clear_run (0 : Fin 19) (0 : Fin 8) 1 regs
    (tapes ell [] [] remainder [] [] encoded)
  have he : clearStacks (0 : Fin 19) (tapes ell [] [] remainder [] [] encoded) =
      tapes ell [] [] [] [] [] encoded := by
    funext i; fin_cases i <;> simp [clearStacks, tapes]
  rw [he] at h
  exact .call _ h

abbrev reverseField : Cmd 8 19 := .call (transferProgram 10 9 0 1)

theorem reverseField_eval (regs : Fin 8 → Bool) (ell encoded : List Bool) :
    Eval reverseField (3 * encoded.length + 3)
      (data regs ell [] [] [] [] [] encoded)
      (data (readRegs regs 0 1 none) ell [] [] [] [] encoded.reverse []) := by
  have h := ListRegisterProgram.transfer_run (10 : Fin 19) 9 (0 : Fin 8) 1
    (by decide) (by decide) regs (tapes ell [] [] [] [] [] encoded)
  have he : transferStacks (10 : Fin 19) 9 (tapes ell [] [] [] [] [] encoded) =
      tapes ell [] [] [] [] encoded.reverse [] := by
    funext i; fin_cases i <;> simp [transferStacks, tapes]
  rw [he] at h
  exact .call _ h

private def straight : List (StructuredProgram.Atom 8 19) → StructuredProgram.Cmd 8 19
  | [] => .skip
  | a :: as => .seq (.atom a) (straight as)

private def straightResult : List (StructuredProgram.Atom 8 19) → Data → Data
  | [], d => d
  | a :: as, d => straightResult as (a.eval d)

private theorem straight_eval (as : List (StructuredProgram.Atom 8 19)) (d : Data) :
    StructuredProgram.Eval (straight as) as.length d (straightResult as d) := by
  induction as generalizing d with
  | nil => exact .skip d
  | cons a as ih =>
      simpa only [straight, straightResult, List.length_cons, Nat.add_comm 1] using
        StructuredProgram.Eval.seq (.atom a d) (ih (a.eval d))

private def resetOps : List (StructuredProgram.Atom 8 19) :=
  [.set 0 false, .set 1 false, .set 2 false, .set 3 false,
    .set 4 false, .set 5 false, .set 6 false, .set 7 false]

abbrev reset : Cmd 8 19 := .base (straight resetOps)

theorem reset_eval (regs : Fin 8 → Bool) (ell payload : List Bool) :
    Eval reset 8 (data regs ell [] [] [] [] payload [])
      (data (fun _ => false) ell [] [] [] [] payload []) := by
  have h := straight_eval resetOps (data regs ell [] [] [] [] payload [])
  have he : straightResult resetOps (data regs ell [] [] [] [] payload []) =
      data (fun _ => false) ell [] [] [] [] payload [] := by
    apply state_ext
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [he] at h
  exact .base (by simpa only [resetOps, List.length_cons, List.length_nil] using h)

abbrev command : Cmd 8 19 := .seq decode (.seq count (.seq divide
  (.seq encode (.seq clearRemainder (.seq reverseField reset)))))

/-- A uniform polynomial bound in the literal's unary index and binary width. -/
def budget (width index : ℕ) : ℕ :=
  (9 * index + 9) + (index * (8 * index + 10) + 4) +
  100 * (width + index + 1) ^ 2 + 32 * (index + 1) * (index + 1) +
  (2 * (width + index) + 3) + (3 * (index + 1) + 3) + 8

theorem command_eval (regs : Fin 8 → Bool) (ell : List Bool) (v : ℕ) (sign : Bool)
    (hell : 0 < BinaryArithmetic.toNat ell) :
    ∃ t ≤ budget ell.length v,
      Eval command t
        (data regs ell [] [] [] []
          (Encoding.encodeNat (2 * v + if sign then 1 else 0)).reverse [])
        (data (fun _ => false) ell [] [] [] []
          (Encoding.encodeNat (v / BinaryArithmetic.toNat ell)).reverse []) := by
  obtain ⟨rd, hd⟩ := decode_eval regs ell v sign
  obtain ⟨nc, hnc, rc, binary, hc, hvalue, hlength⟩ :=
    count_eval rd ell (List.replicate v true)
  simp only [List.length_replicate] at hnc hvalue hlength
  obtain ⟨nd, hnd, rq, hq⟩ := divide_eval rc ell binary
  obtain ⟨ne, hne, re, he⟩ := encode_eval rq ell
    (ModularQuotientArithmetic.divide ell binary).2 (ModularQuotientArithmetic.divide ell binary).1
  have hquot : BinaryArithmetic.toNat (ModularQuotientArithmetic.divide ell binary).1 =
      v / BinaryArithmetic.toNat ell := by
    rw [ModularQuotientArithmetic.divide_quotient_correct ell binary hell, hvalue]
  rw [hquot] at he
  have hremLength := ModularQuotientArithmetic.divide_remainder_length ell binary
  have hquotLength := ModularQuotientArithmetic.divide_quotient_length ell binary
  have hclear := clearRemainder_eval re ell (ModularQuotientArithmetic.divide ell binary).2
    (Encoding.encodeNat (v / BinaryArithmetic.toNat ell))
  have hrev := reverseField_eval (readRegs re 0 1 none) ell
    (Encoding.encodeNat (v / BinaryArithmetic.toNat ell))
  have hreset := reset_eval (readRegs (readRegs re 0 1 none) 0 1 none) ell
    (Encoding.encodeNat (v / BinaryArithmetic.toNat ell)).reverse
  have h := hd.seq (hc.seq (hq.seq (he.seq (hclear.seq (hrev.seq hreset)))))
  refine ⟨_, ?_, h⟩
  have hdiv := Nat.div_le_self v (BinaryArithmetic.toNat ell)
  have hdivCost : nd ≤ 100 * (ell.length + v + 1) ^ 2 := hnd.trans
    (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (by omega) 2))
  have hconvCost : ne ≤ 32 * (v + 1) * (v + 1) := by
    unfold CounterConversions.runtimeBound at hne
    rw [CounterPrograms.value_eq_toNat, hquot, hquotLength] at hne
    exact hne.trans (Nat.mul_le_mul
      (Nat.mul_le_mul_left 32 (Nat.add_le_add_right hdiv 1))
      (Nat.add_le_add_right hlength 1))
  have hfieldLength : (Encoding.encodeNat (v / BinaryArithmetic.toNat ell)).length =
      v / BinaryArithmetic.toNat ell + 1 := by simp [Encoding.encodeNat]
  unfold budget
  rw [hremLength, hfieldLength]
  split <;> omega

def program := compiled command (9 : Fin 19) 9

/-- The parser-facing contract accepts the canonical code directly. -/
theorem command_eval_code (regs : Fin 8 → Bool) (ell : List Bool) (code : ℕ)
    (hell : 0 < BinaryArithmetic.toNat ell) :
    ∃ t ≤ budget ell.length (code / 2),
      Eval command t
        (data regs ell [] [] [] [] (Encoding.encodeNat code).reverse [])
        (data (fun _ => false) ell [] [] [] []
          (Encoding.encodeNat ((code / 2) / BinaryArithmetic.toNat ell)).reverse []) := by
  have hdecomp : 2 * (code / 2) + (if decide (code % 2 = 1) then 1 else 0) = code := by
    have hm := Nat.mod_lt code (by omega : 0 < 2)
    have hd := Nat.mod_add_div code 2
    by_cases h : code % 2 = 1 <;> simp [h] <;> omega
  simpa only [hdecomp] using command_eval regs ell (code / 2) (decide (code % 2 = 1)) hell

theorem program_runsIn (regs : Fin 8 → Bool) (ell : List Bool) (v : ℕ) (sign : Bool)
    (hell : 0 < BinaryArithmetic.toNat ell) :
    RunsIn program (budget ell.length v + 1)
      ((data regs ell [] [] [] []
        (Encoding.encodeNat (2 * v + if sign then 1 else 0)).reverse []).withPC (some program.entry))
      ((data (fun _ => false) ell [] [] [] []
        (Encoding.encodeNat (v / BinaryArithmetic.toNat ell)).reverse []).withPC none) := by
  obtain ⟨t, ht, he⟩ := command_eval regs ell v sign hell
  exact ⟨t + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 9 9⟩

end SubexponentialSAT.SubexpLiteralChunkProgram

end OAI.Algorithms
