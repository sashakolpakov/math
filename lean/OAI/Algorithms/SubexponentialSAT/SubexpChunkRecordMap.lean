import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLiteralChunkProgram
import OAI.Algorithms.SubexponentialSAT.ExecLiteralDedupProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-!
# Actual map from literal records to chunk records

The input is the canonical encoded list of literal codes and a preserved binary
chunk width. Each parsed record passes through the actual index decoder,
counter, division program, and record writer. The accumulator is reversed, as
required by the separately checked record-reversal and stable-deduplication
passes. No semantic map is installed as a machine instruction.
-/

namespace SubexponentialSAT.SubexpChunkRecordMap

open BitProgram StructuredCalls

abbrev Data := State 11 22

def regs (v pr found : Bool) : Fin 11 → Bool := fun i =>
  if i = 8 then v else if i = 9 then pr else if i = 10 then found else false

def tapes (ell source output payload : List Bool) : Fin 22 → List Bool := fun i =>
  if i = 9 then payload else if i = 18 then ell else if i = 19 then source
  else if i = 20 then output else []

def data (v pr found : Bool) (ell source output payload : List Bool) : Data :=
  ⟨regs v pr found, tapes ell source output payload⟩

private theorem state_ext {r s : ℕ} {a b : State r s}
    (hr : a.regs = b.regs) (hs : a.stacks = b.stacks) : a = b := by
  cases a; cases b; simp_all

def ports : RecordPrograms.Ports 11 22 where
  tag := 8
  present := 9
  found := 10
  source := 19
  payload := 9
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

theorem parser_state (v pr found v' pr' found' : Bool)
    (ell source output payload source' payload' : List Bool) :
    RecordPrograms.state ports (data v pr found ell source output payload)
        v' pr' found' source' payload' = data v' pr' found' ell source' output payload' := by
  apply state_ext
  · funext i; fin_cases i <;> rfl
  · funext i; fin_cases i <;> rfl

def convertRegisters : Fin 8 → Fin 11 := Fin.castAdd 3
def convertStacks : Fin 19 → Fin 22 := Fin.castAdd 3

theorem convertRegisters_injective : Function.Injective convertRegisters := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 11 => x.val) h)
theorem convertStacks_injective : Function.Injective convertStacks := by
  intro i j h; exact Fin.ext (congrArg (fun x : Fin 22 => x.val) h)

abbrev convert : Cmd 11 22 := .call (ProgramLinking.liftProgram
  SubexpLiteralChunkProgram.program convertRegisters convertStacks)

private theorem embed_convert (v pr found : Bool)
    (ell source output oldPayload payload : List Bool) :
    embedState convertRegisters convertStacks
      (data v pr found ell source output oldPayload)
      (SubexpLiteralChunkProgram.data (fun _ => false) ell [] [] [] [] payload []) =
      data v pr found ell source output payload := by
  apply embedState_eq_of_ports _ _ _ _ _ convertRegisters_injective convertStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi; rfl
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h9 : i ≠ 9 := fun h => hi ⟨9, h.symm⟩
    simp only [data, tapes, h9, ite_false]

theorem convert_eval (ell source output : List Bool) (code : ℕ) (v pr found : Bool)
    (hell : 0 < BinaryArithmetic.toNat ell) :
    ∃ t ≤ SubexpLiteralChunkProgram.budget ell.length (code / 2) + 1,
      Eval convert t
        (data v pr found ell source output (Encoding.encodeNat code).reverse)
        (data v pr found ell source output
          (Encoding.encodeNat ((code / 2) / BinaryArithmetic.toNat ell)).reverse) := by
  obtain ⟨t, ht, he⟩ := SubexpLiteralChunkProgram.command_eval_code
    (fun _ => false) ell code hell
  have htrace := compiled_halt_trace he (9 : Fin 19) 9
  have h := eval_call_lifted SubexpLiteralChunkProgram.program convertRegisters convertStacks
    (data v pr found ell source output (Encoding.encodeNat code).reverse)
    convertRegisters_injective convertStacks_injective htrace
  simp only [embed_convert] at h
  exact ⟨t + 1, Nat.add_le_add_right ht 1, h⟩

def emitRegisters : Fin 3 → Fin 11 := ![8, 9, 10]
def emitStacks : Fin 4 → Fin 22 := ![19, 21, 20, 9]

theorem emitRegisters_injective : Function.Injective emitRegisters := by decide
theorem emitStacks_injective : Function.Injective emitStacks := by decide

abbrev emit : Cmd 11 22 := .call (ProgramLinking.liftProgram
  SubexpNormalizeProgram.emitIfSelectedProgram emitRegisters emitStacks)

private theorem embed_emit (v pr found oldV oldPr oldFound : Bool)
    (ell source output payload oldOutput oldPayload : List Bool) :
    embedState emitRegisters emitStacks
      (data oldV oldPr oldFound ell source oldOutput oldPayload)
      (SubexpNormalizeProgram.filterState v pr found source [] output payload) =
      data v pr found ell source output payload := by
  apply embedState_eq_of_ports _ _ _ _ _ emitRegisters_injective emitStacks_injective
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h8 : i ≠ 8 := fun h => hi ⟨0, h.symm⟩
    have h9 : i ≠ 9 := fun h => hi ⟨1, h.symm⟩
    have h10 : i ≠ 10 := fun h => hi ⟨2, h.symm⟩
    simp only [data, regs, h8, h9, h10, ite_false]
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h9 : i ≠ 9 := fun h => hi ⟨3, h.symm⟩
    have h20 : i ≠ 20 := fun h => hi ⟨2, h.symm⟩
    simp only [data, tapes, h9, h20, ite_false]

theorem emit_eval (ell source output bits : List Bool) (v pr : Bool) :
    Eval emit (5 * bits.length + 12)
      (data v pr true ell source output bits.reverse)
      (data false true false ell source (true :: (Encoding.frame bits ++ output)) []) := by
  have h := eval_call_lifted SubexpNormalizeProgram.emitIfSelectedProgram
    emitRegisters emitStacks (data v pr true ell source output bits.reverse)
    emitRegisters_injective emitStacks_injective
    (SubexpNormalizeProgram.emitIfSelected_trace true bits source [] output v pr)
  simpa only [embed_emit, SubexpNormalizeProgram.emitIfSelectedSteps, ite_true,
    Nat.add_assoc] using h

abbrev select : Cmd 11 22 := .base (.atom (.set 10 true))

theorem select_eval (v pr found : Bool) (ell source output payload : List Bool) :
    Eval select 1 (data v pr found ell source output payload)
      (data v pr true ell source output payload) := by
  have h := StructuredProgram.Eval.atom (StructuredProgram.Atom.set (r := 11) (s := 22) 10 true)
    (data v pr found ell source output payload)
  have he : (StructuredProgram.Atom.set (r := 11) (s := 22) 10 true).eval
      (data v pr found ell source output payload) = data v pr true ell source output payload := by
    apply state_ext
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [he] at h
  exact .base h

abbrev callback : Cmd 11 22 := .seq convert (.seq select emit)

def chunk (ell : List Bool) (code : ℕ) : ℕ := (code / 2) / BinaryArithmetic.toNat ell

theorem callback_eval (ell source output : List Bool) (code : ℕ)
    (hell : 0 < BinaryArithmetic.toNat ell) :
    ∃ t ≤ SubexpLiteralChunkProgram.budget ell.length (code / 2) +
        5 * (Encoding.encodeNat (chunk ell code)).length + 14,
      Eval callback t
        (data false true false ell source output (Encoding.encodeNat code).reverse)
        (data false true false ell source
          (true :: (Encoding.frame (Encoding.encodeNat (chunk ell code)) ++ output)) []) := by
  obtain ⟨t, ht, hc⟩ := convert_eval ell source output code false true false hell
  have hs := select_eval false true false ell source output
    (Encoding.encodeNat (chunk ell code)).reverse
  have he := emit_eval ell source output (Encoding.encodeNat (chunk ell code)) false true
  exact ⟨t + (1 + (5 * (Encoding.encodeNat (chunk ell code)).length + 12)),
    by omega, hc.seq (hs.seq he)⟩

def mappedBits (ell bits : List Bool) : List Bool :=
  Encoding.encodeNat (chunk ell (bits.length - 1))

@[simp] theorem mappedBits_encodeNat (ell : List Bool) (code : ℕ) :
    mappedBits ell (Encoding.encodeNat code) = Encoding.encodeNat (chunk ell code) := by
  simp [mappedBits]

def callbackCost (ell bits : List Bool) : ℕ :=
  SubexpLiteralChunkProgram.budget ell.length ((bits.length - 1) / 2) +
    5 * (mappedBits ell bits).length + 14

def Invariant (ell : List Bool) (d : Data) : Prop :=
  ∃ output, d = data false false false ell [] output []

def effect (ell bits : List Bool) (a b : Data) : Prop :=
  b.stacks 20 = true :: (Encoding.frame (mappedBits ell bits) ++ a.stacks 20)

def Canonical (bits : List Bool) : Prop := ∃ code, bits = Encoding.encodeNat code

theorem callback_contract (ell : List Bool) (hell : 0 < BinaryArithmetic.toNat ell) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (callbackCost ell) (Invariant ell) (effect ell) Canonical := by
  intro bits tail base hbits hbase
  rcases hbits with ⟨code, rfl⟩
  rcases hbase with ⟨output, rfl⟩
  obtain ⟨t, ht, he⟩ := callback_eval ell tail output code hell
  let out := true :: (Encoding.frame (Encoding.encodeNat (chunk ell code)) ++ output)
  refine ⟨t, data false false false ell [] out [], ?_, ⟨out, rfl⟩, ?_, ?_⟩
  · simpa only [callbackCost, Encoding.length_encodeNat, Nat.add_sub_cancel,
      mappedBits_encodeNat] using ht
  · change out = true :: (Encoding.frame (mappedBits ell (Encoding.encodeNat code)) ++ output)
    rw [mappedBits_encodeNat]
  · simpa only [parser_state] using he

theorem visits_output (ell : List Bool) {records : List (List Bool)} {base next : Data}
    (h : RecordPrograms.Visits (fun _ => false) (effect ell) records base next)
    (acc : List (List Bool)) (hacc : base.stacks 20 = Encoding.encodeList id acc) :
    next.stacks 20 = Encoding.encodeList id ((records.map (mappedBits ell)).reverse ++ acc) := by
  induction h generalizing acc with
  | nil base => simpa using hacc
  | hit ht he => simp at ht
  | @miss bits rest base middle next ht he history ih =>
      have hm : middle.stacks 20 = Encoding.encodeList id (mappedBits ell bits :: acc) := by
        simpa only [effect, hacc, Encoding.encodeList, id_eq] using he
      have hnext := ih (mappedBits ell bits :: acc) hm
      simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
        List.singleton_append] using hnext

abbrev scan : Cmd 11 22 := RecordPrograms.iterate ports callback

theorem scan_eval (ell : List Bool) (codes acc : List ℕ) (suffix : List Bool)
    (hell : 0 < BinaryArithmetic.toNat ell) (v pr found : Bool) :
    ∃ t ≤ 3 + RecordPrograms.budget (callbackCost ell) (codes.map Encoding.encodeNat),
      Eval scan t
        (data v pr found ell (Encoding.encodeList Encoding.encodeNat codes ++ suffix)
          (Encoding.encodeList Encoding.encodeNat acc) [])
        (data false true false ell suffix
          (Encoding.encodeList Encoding.encodeNat ((codes.map (chunk ell)).reverse ++ acc)) []) := by
  let base := data false false false ell [] (Encoding.encodeList Encoding.encodeNat acc) []
  obtain ⟨t, next, ht, hnext, hh, he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (callbackCost ell) (Invariant ell) (effect ell) Canonical
    (callback_contract ell hell) (codes.map Encoding.encodeNat) suffix base
    (by intro bits hb; rcases List.mem_map.mp hb with ⟨code, _, rfl⟩; exact ⟨code, rfl⟩)
    ⟨Encoding.encodeList Encoding.encodeNat acc, rfl⟩ v pr found
  have hout := visits_output ell hh (acc.map Encoding.encodeNat)
    (by exact (ExecLiteralDedupProgram.encode_nat_records acc).symm)
  rcases hnext with ⟨out, rfl⟩
  have hout' : out = Encoding.encodeList Encoding.encodeNat
      ((codes.map (chunk ell)).reverse ++ acc) := by
    change out = _ at hout
    have hmaps : (codes.map Encoding.encodeNat).map (mappedBits ell) =
        (codes.map (chunk ell)).map Encoding.encodeNat := by
      simp only [List.map_map, Function.comp_def, mappedBits_encodeNat]
    rw [hmaps, ← List.map_reverse, ← List.map_append,
      ExecLiteralDedupProgram.encode_nat_records] at hout
    exact hout
  have hany : (codes.map Encoding.encodeNat).any (fun _ => false) = false := by simp
  rw [hout'] at he
  refine ⟨t, ht, ?_⟩
  simpa only [scan, base, parser_state, ExecLiteralDedupProgram.encode_nat_records,
    hany, SubexpNormalizeProgram.unread_false] using he

end SubexponentialSAT.SubexpChunkRecordMap

end OAI.Algorithms
