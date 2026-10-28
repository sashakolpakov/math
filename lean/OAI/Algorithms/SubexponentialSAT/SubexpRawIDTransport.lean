import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawIDTransportCore
import OAI.Algorithms.SubexponentialSAT.Subexp.RawIdCollectProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.RawIdRenameBounds
import OAI.Algorithms.SubexponentialSAT.BitProgramCompile

namespace OAI.Algorithms

/-! The closed raw-ID transport: actual identifier collection, stable
deduplication, dictionary counting, dictionary-index renaming, and clean
unary-header output. All finite code is independent of the input formula. -/

namespace SubexponentialSAT.SubexpRawIDTransport

open BitProgram StructuredCalls
open Subexp

attribute [local simp] Fin.coe_ofNat_eq_mod

def collectedWord (F : RawIdEncoding.Formula) : Word :=
  Encoding.encodeList id (RawIdEncoding.ids F).reverse
def dictionaryWord (F : RawIdEncoding.Formula) : Word :=
  Encoding.encodeList id (RawIdEncoding.dictionary F)
def bodyWord (F : RawIdEncoding.Formula) : Word :=
  Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (RawIdRenaming.physicalCodes F)

theorem collector_state (regs : Fin 8 → Bool) (source collected raw : Word) :
    RawIdCollectProgram.resting regs source collected =
      parserState regs {source := source, collected := collected, raw := raw} := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [
 RawIdCollectProgram.store, parserStacks, store]

theorem renamer_state (regs : Fin 8 → Bool) (dictionary source output dimension : Word) :
    RawIdRenameProgram.resting regs dictionary source output =
      parserState regs {source := source, dictionary := dictionary, output := output, dimension := dimension} := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [
      RawIdRenameProgram.baseView, RawIdRenameProgram.store,
 parserStacks, store]

def collect : Command := .call (ProgramLinking.liftProgram
  RawIdCollectProgram.program parserRegisters parserStacks)
def rename : Command := .call (ProgramLinking.liftProgram
  RawIdRenameProgram.program parserRegisters parserStacks)

theorem collect_eval (regs : Fin 10 → Bool) (F : RawIdEncoding.Formula) :
    ∃ n ≤ 50 * ((RawIdEncoding.encode F).length + 1), ∃ rf,
      Eval collect n
        (state regs {source := RawIdEncoding.encode F, raw := RawIdEncoding.encode F})
        (state rf {collected := collectedWord F, raw := RawIdEncoding.encode F}) := by
  obtain ⟨rf, n, hn, ht⟩ := RawIdCollectProgram.program_linear (regs ∘ parserRegisters) F
  let v : View := {source := RawIdEncoding.encode F, raw := RawIdEncoding.encode F}
  let w : View := {collected := collectedWord F, raw := RawIdEncoding.encode F}
  have ha : RawIdCollectProgram.resting (regs ∘ parserRegisters) (RawIdEncoding.encode F) [] =
      projectState parserRegisters parserStacks (state regs v) :=
    collector_state _ _ _ _
  have hb : RawIdCollectProgram.resting rf [] (collectedWord F) = parserState rf w :=
    collector_state _ _ _ _
  change Trace RawIdCollectProgram.program n
    ((RawIdCollectProgram.resting (regs ∘ parserRegisters) (RawIdEncoding.encode F) []).withPC _)
    ((RawIdCollectProgram.resting rf [] (collectedWord F)).withPC _) at ht
  rw [ha, hb] at ht
  have he := eval_call_from_state RawIdCollectProgram.program parserRegisters parserStacks
    (state regs v) parserRegisters_injective parserStacks_injective ht
  rw [parserState_install regs rf v w rfl rfl] at he
  exact ⟨n, hn, parserResultRegs regs rf, he⟩

theorem rename_eval (regs : Fin 10 → Bool) (F : RawIdEncoding.Formula) :
    ∃ n ≤ 32000 * ((RawIdEncoding.encode F).length + 1)^6, ∃ rf,
      Eval rename n
        (state regs {source := RawIdEncoding.encode F, dictionary := dictionaryWord F, dimension := List.replicate (RawIdEncoding.dimension F) true})
        (state rf {dictionary := dictionaryWord F, output := bodyWord F, dimension := List.replicate (RawIdEncoding.dimension F) true}) := by
  obtain ⟨rf, n, hn, ht⟩ := RawIdRenameBounds.renamed_polynomial (regs ∘ parserRegisters) F
  let v : View := {source := RawIdEncoding.encode F, dictionary := dictionaryWord F, dimension := List.replicate (RawIdEncoding.dimension F) true}
  let w : View := {dictionary := dictionaryWord F, output := bodyWord F, dimension := List.replicate (RawIdEncoding.dimension F) true}
  have ha : RawIdRenameProgram.resting (regs ∘ parserRegisters) (dictionaryWord F)
      (RawIdEncoding.encode F) [] = projectState parserRegisters parserStacks (state regs v) :=
    renamer_state _ _ _ _ _
  have hb : RawIdRenameProgram.resting rf (dictionaryWord F) [] (bodyWord F) = parserState rf w :=
    renamer_state _ _ _ _ _
  change Trace RawIdRenameProgram.program n
    ((RawIdRenameProgram.resting (regs ∘ parserRegisters) (dictionaryWord F)
      (RawIdEncoding.encode F) []).withPC _) ((RawIdRenameProgram.resting rf
      (dictionaryWord F) [] (bodyWord F)).withPC _) at ht
  rw [ha, hb] at ht
  have he := eval_call_from_state RawIdRenameProgram.program parserRegisters parserStacks
    (state regs v) parserRegisters_injective parserStacks_injective ht
  rw [parserState_install regs rf v w rfl rfl] at he
  exact ⟨n, hn, parserResultRegs regs rf, he⟩

def command : Command := .seq copyRaw (.seq collect (.seq moveCollected (.seq dedupCall
  (.seq moveDictionary (.seq copyDictionary (.seq countCall (.seq restoreRaw (.seq rename finish))))))))
abbrev program : Program 10 24 (size command + 1) := compiled command 23 8

def overhead (F : RawIdEncoding.Formula) : ℕ :=
  16 * (RawIdEncoding.encode F).length + 9 * (collectedWord F).length +
    18 * (dictionaryWord F).length + 3 * RawIdEncoding.dimension F +
      SubexpSunflowerProgram.CountRecords.loopSteps (RawIdEncoding.dictionary F) + 53

def runtimeBound (F : RawIdEncoding.Formula) : ℕ := overhead F +
  50 * ((RawIdEncoding.encode F).length + 1) +
    120 * ((collectedWord F).length + 1)^2 +
      32000 * ((RawIdEncoding.encode F).length + 1)^6

theorem command_eval (regs : Fin 10 → Bool) (F : RawIdEncoding.Formula) :
    ∃ n, Eval command n (state regs {raw := RawIdEncoding.encode F})
      (StructuredProgram.ioState (8 : Fin 24) (RawIdRenaming.outputWord F)) ∧
      n + 1 ≤ runtimeBound F := by
  have h0 := copyRaw_eval regs (RawIdEncoding.encode F)
  obtain ⟨n1, hn1, r1, h1⟩ := collect_eval (readRegs regs 0 1 none) F
  have h2 := moveCollected_eval r1 (collectedWord F) (RawIdEncoding.encode F)
  obtain ⟨n3, hn3, r3, h3⟩ := dedupCall_eval (readRegs r1 0 1 none)
    (RawIdEncoding.ids F).reverse (RawIdEncoding.encode F)
  change Eval dedupCall n3 (state _ {source := collectedWord F, raw := RawIdEncoding.encode F})
    (state r3 {source := dictionaryWord F, raw := RawIdEncoding.encode F}) at h3
  have h4 := moveDictionary_eval r3 (dictionaryWord F) (RawIdEncoding.encode F)
  have h5 := copyDictionary_eval (readRegs r3 0 1 none) (dictionaryWord F) (RawIdEncoding.encode F)
  have h6 := countCall_eval (readRegs (readRegs r3 0 1 none) 0 1 none)
    (RawIdEncoding.dictionary F) (RawIdEncoding.encode F)
  have h7 := restoreRaw_eval (readRegs (readRegs (readRegs r3 0 1 none) 0 1 none) 0 1 none)
    (dictionaryWord F) (List.replicate (RawIdEncoding.dimension F) true) (RawIdEncoding.encode F)
  obtain ⟨n8, hn8, r8, h8⟩ := rename_eval
    (readRegs (readRegs (readRegs (readRegs r3 0 1 none) 0 1 none) 0 1 none) 0 1 none) F
  have h9 := finish_eval r8 (dictionaryWord F) (bodyWord F) (RawIdEncoding.dimension F)
  have he := h0.seq (h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq (h8.seq h9))))))))
  refine ⟨_, he, ?_⟩
  unfold runtimeBound overhead
  change n3 ≤ 120 * ((collectedWord F).length + 1)^2 at hn3
  omega

theorem countSteps_le (records : List Word) :
    SubexpSunflowerProgram.CountRecords.loopSteps records ≤
      4 * ((Encoding.encodeList id records).length + 1) := by
  have h := ProgramEncoding.encodeRecords_length records
  change (Encoding.encodeList id records).length = _ at h
  unfold SubexpSunflowerProgram.CountRecords.loopSteps
  omega

theorem runtimeBound_polynomial (F : RawIdEncoding.Formula) :
    runtimeBound F ≤ 40000 * ((RawIdEncoding.encode F).length + 1)^6 := by
  let K := (RawIdEncoding.encode F).length + 1
  have hK : 1 ≤ K := by dsimp [K]; omega
  have h16 : K ≤ K^6 := by simpa using Nat.pow_le_pow_right hK (show 1 ≤ 6 by decide)
  have h26 : K^2 ≤ K^6 := Nat.pow_le_pow_right hK (by decide)
  have h46 : K^4 ≤ K^6 := Nat.pow_le_pow_right hK (by decide)
  have h1 : 1 ≤ K^6 := Nat.one_le_pow _ _ hK
  have h2 : 1 ≤ K^2 := Nat.one_le_pow _ _ hK
  have hi := RawIdRenaming.collected_bytes_le F
  have hd := RawIdRenaming.dictionary_bytes_le F
  have hn := RawIdEncoding.dimension_le_bytes F
  change (collectedWord F).length ≤ 3 * K^2 at hi
  change (dictionaryWord F).length ≤ 3 * K^2 at hd
  have hl : (RawIdEncoding.encode F).length ≤ K^6 :=
    (show (RawIdEncoding.encode F).length ≤ K by dsimp [K]; omega).trans h16
  have hi6 : (collectedWord F).length ≤ 3 * K^6 := by omega
  have hd6 : (dictionaryWord F).length ≤ 3 * K^6 := by omega
  have hcount := countSteps_le (RawIdEncoding.dictionary F)
  change SubexpSunflowerProgram.CountRecords.loopSteps (RawIdEncoding.dictionary F) ≤
    4 * ((dictionaryWord F).length + 1) at hcount
  have hic : (collectedWord F).length + 1 ≤ 4 * K^2 := by omega
  have hdup : 120 * ((collectedWord F).length + 1)^2 ≤ 1920 * K^6 := by
    calc
      _ ≤ 120 * (4 * K^2)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hic 2)
      _ = 1920 * K^4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ h46
  unfold runtimeBound overhead
  change 16 * (RawIdEncoding.encode F).length + 9 * (collectedWord F).length +
    18 * (dictionaryWord F).length + 3 * RawIdEncoding.dimension F +
      SubexpSunflowerProgram.CountRecords.loopSteps (RawIdEncoding.dictionary F) + 53 +
        50 * K + 120 * ((collectedWord F).length + 1)^2 + 32000 * K^6 ≤ 40000 * K^6
  omega

theorem input_state (regs : Fin 10 → Bool) (word : Word) :
    state regs {raw := word} = ⟨regs, fun i => if i = (23 : Fin 24) then word else []⟩ := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    by_cases hi : i = 23 <;> simp [ store, hi]

theorem program_runsIn (F : RawIdEncoding.Formula) :
    RunsIn program (runtimeBound F) (initial program (RawIdEncoding.encode F))
      ((StructuredProgram.ioState (8 : Fin 24) (RawIdRenaming.outputWord F)).withPC none) := by
  obtain ⟨n, he, hn⟩ := command_eval (fun _ => false) F
  refine ⟨n + 1, hn, ?_⟩
  have hinput : StructuredProgram.ioState (23 : Fin 24) (RawIdEncoding.encode F) =
      state (fun _ => false) {raw := RawIdEncoding.encode F} := by
    symm
    simpa [StructuredProgram.ioState] using
      input_state (fun _ => false) (RawIdEncoding.encode F)
  change Trace (compiled command 23 8) (n + 1)
    ((StructuredProgram.ioState 23 (RawIdEncoding.encode F)).withPC
      (some (compiled command 23 8).entry)) _
  rw [hinput]
  simpa only [input_state] using compiled_halt_trace he 23 8

theorem polynomial_runs (F : RawIdEncoding.Formula) :
    RunsIn program (40000 * ((RawIdEncoding.encode F).length + 1)^6)
      (initial program (RawIdEncoding.encode F))
      ((StructuredProgram.ioState (8 : Fin 24) (RawIdRenaming.outputWord F)).withPC none) :=
  (program_runsIn F).mono (runtimeBound_polynomial F)

end SubexponentialSAT.SubexpRawIDTransport

end OAI.Algorithms
