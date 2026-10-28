import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixImageServices

namespace OAI.Algorithms

/-! The concrete record callback and tuple-generation driver for matrix-image
enumeration. Every arithmetic call below is the fixed matrix-vector program. -/

namespace SubexponentialSAT.Subexp.MatrixImageEnumeration

open BitProgram StructuredCalls SubexpScanPrimitives
open MatrixWordEncoding BlockCoefficientProgram

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

def cleared (d : Data) (src : Fin 32) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem clear_eval (d : Data) (src : Fin 32) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (cleared d src) := by
  simpa only [clear, cleared, StackRoutines.clearStacks] using
    TupleProgram.clear_eval src (0 : Fin 13) 1 d

abbrev restore : Cmd 13 32 := .seq (.base (.atom (.set 10 false)))
  (.seq (.base (.atom (.set 11 true))) (.base (.atom (.set 12 false))))

def restored (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 10 false) 11 true) 12 false,
    d.stacks⟩

theorem restore_eval (d : Data) : Eval restore 3 d (restored d) := by
  have h1 := Eval.base (StructuredProgram.Eval.atom (.set (10 : Fin 13) false) d)
  have h2 := Eval.base (StructuredProgram.Eval.atom (.set (11 : Fin 13) true)
    ((StructuredProgram.Atom.set (10 : Fin 13) false).eval d))
  have h3 := Eval.base (StructuredProgram.Eval.atom (.set (12 : Fin 13) false)
    ((StructuredProgram.Atom.set (11 : Fin 13) true).eval
      ((StructuredProgram.Atom.set (10 : Fin 13) false).eval d)))
  simpa [restore, restored, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h1.seq (h2.seq h3)

abbrev callback : Cmd 13 32 :=
  .seq (transfer 21 12) (.seq (copy 16 11) (.seq (copy 17 15)
    (.seq matrix (.seq (copy 17 15) (.seq flatten
      (.seq (clear 12) (.seq emit restore)))))))

def callbackBudget (p : ℕ) {m n : ℕ} (M : Fin m → Fin n → ZMod p)
    (bits : List Bool) : ℕ :=
  (3 * bits.length + 3) + (7 * (matrixBits p M).length + 5) + (7 * m + 5) +
  MatrixVectorProgram.matrixBudget m n (width p) + (7 * m + 5) +
  (9 * (m * width p) + 6 * m + 7) + (2 * bits.length + 3) +
  (8 * (m * width p) + 10) + 3

/-- Stack bookkeeping is normalized in small port blocks independently of
execution traces. This keeps the finite-map proof bounded and reusable. -/
private def callbackExitState (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (regs : Fin 13 → Bool) (rm : Fin 8 → Bool)
    (bits : List Bool) (result : List (List Bool)) (tail output : List Bool) : Data :=
  let d0 := RecordPrograms.state ports (stored p M regs [] [] output)
    false true false tail bits.reverse
  let d1 := afterTransfer d0 21 12 0 1
  let d2 := afterCopy d1 16 11 0 1
  let d3 := afterCopy d2 17 15 0 1
  let d4 := withMatrix d3 (MatrixScalarProgram.state rm [] [] (modulus p)
    (MatrixProgramSupport.words result) [] [] bits [] (zero p) [])
  let d5 := afterCopy d4 17 15 0 1
  restored (emitted (cleared (flattened d5 result.flatten) 12))

private def callbackOutputStacks (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (tail output : List Bool) : Fin 32 → List Bool :=
  (RecordPrograms.state ports (stored p M (fun _ => false) [] [] output)
    false true false tail []).stacks

private theorem callback_stacks_0 (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (regs : Fin 13 → Bool) (rm : Fin 8 → Bool)
    (bits : List Bool) (result : List (List Bool)) (tail output : List Bool) (i : Fin 8) :
    (callbackExitState p M regs rm bits result tail output).stacks (Fin.castAdd 24 i) =
      callbackOutputStacks p M tail (TupleProgram.prependRecord result.flatten output)
        (Fin.castAdd 24 i) := by
  fin_cases i <;>
    simp [callbackExitState, callbackOutputStacks, restored, emitted, cleared, flattened,
      afterCopy, StackRoutines.copyStacks, withMatrix,
      MatrixScalarProgram.scalarStacks, afterTransfer, StackRoutines.transferStacks,
      RecordPrograms.state, ports, stored]

private theorem callback_stacks_1 (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (regs : Fin 13 → Bool) (rm : Fin 8 → Bool)
    (bits : List Bool) (result : List (List Bool)) (tail output : List Bool) (i : Fin 8) :
    (callbackExitState p M regs rm bits result tail output).stacks (Fin.natAdd 8 (Fin.castAdd 16 i)) =
      callbackOutputStacks p M tail (TupleProgram.prependRecord result.flatten output)
        (Fin.natAdd 8 (Fin.castAdd 16 i)) := by
  fin_cases i <;>
    simp [callbackExitState, callbackOutputStacks, restored, emitted, cleared, flattened,
      afterCopy, StackRoutines.copyStacks, withMatrix,
      MatrixScalarProgram.scalarStacks, afterTransfer, StackRoutines.transferStacks,
      RecordPrograms.state, ports, stored]

private theorem callback_stacks_2 (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (regs : Fin 13 → Bool) (rm : Fin 8 → Bool)
    (bits : List Bool) (result : List (List Bool)) (tail output : List Bool) (i : Fin 8) :
    (callbackExitState p M regs rm bits result tail output).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 8 i))) =
      callbackOutputStacks p M tail (TupleProgram.prependRecord result.flatten output)
        (Fin.natAdd 8 (Fin.natAdd 8 (Fin.castAdd 8 i))) := by
  fin_cases i <;>
    simp [callbackExitState, callbackOutputStacks, restored, emitted, cleared, flattened,
      afterCopy, StackRoutines.copyStacks, withMatrix,
      MatrixScalarProgram.scalarStacks, afterTransfer, StackRoutines.transferStacks,
      RecordPrograms.state, ports, stored]

private theorem callback_stacks_3 (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (regs : Fin 13 → Bool) (rm : Fin 8 → Bool)
    (bits : List Bool) (result : List (List Bool)) (tail output : List Bool) (i : Fin 8) :
    (callbackExitState p M regs rm bits result tail output).stacks (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 i))) =
      callbackOutputStacks p M tail (TupleProgram.prependRecord result.flatten output)
        (Fin.natAdd 8 (Fin.natAdd 8 (Fin.natAdd 8 i))) := by
  fin_cases i <;>
    simp [callbackExitState, callbackOutputStacks, restored, emitted, cleared, flattened,
      afterCopy, StackRoutines.copyStacks, withMatrix,
      MatrixScalarProgram.scalarStacks, afterTransfer, StackRoutines.transferStacks,
      RecordPrograms.state, ports, stored]

private theorem callback_final_stacks (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (regs : Fin 13 → Bool) (rm : Fin 8 → Bool)
    (bits : List Bool) (result : List (List Bool)) (tail output : List Bool) :
    (callbackExitState p M regs rm bits result tail output).stacks =
      callbackOutputStacks p M tail (TupleProgram.prependRecord result.flatten output) := by
  funext j
  refine Fin.addCases (m := 8) (n := 24) (fun i => ?_) (fun j => ?_) j
  · exact callback_stacks_0 p M regs rm bits result tail output i
  · refine Fin.addCases (m := 8) (n := 16) (fun i => ?_) (fun j => ?_) j
    · exact callback_stacks_1 p M regs rm bits result tail output i
    · refine Fin.addCases (m := 8) (n := 8) (fun i => ?_) (fun i => ?_) j
      · exact callback_stacks_2 p M regs rm bits result tail output i
      · exact callback_stacks_3 p M regs rm bits result tail output i

theorem callback_eval (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (v : Fin n → ZMod p)
    (regs : Fin 13 → Bool) (tail output : List Bool) :
    ∃ t ≤ callbackBudget p M (MatrixProgramSupport.words (vectorWords p v)), ∃ rf,
      Eval callback t
        (RecordPrograms.state ports (stored p M regs [] [] output) false true false tail
          (MatrixProgramSupport.words (vectorWords p v)).reverse)
        (RecordPrograms.state ports
          (stored p M rf [] [] (TupleProgram.prependRecord (bank p M v) output))
          false true false tail []) := by
  let bits := MatrixProgramSupport.words (vectorWords p v)
  let d0 := RecordPrograms.state ports (stored p M regs [] [] output) false true false tail bits.reverse
  let d1 := afterTransfer d0 21 12 0 1
  let d2 := afterCopy d1 16 11 0 1
  let d3 := afterCopy d2 17 15 0 1
  have h1 : Eval (transfer 21 12) (3 * bits.length + 3) d0 d1 := by
    have hl : (d0.stacks 21).length = bits.length := by
      simp [d0, RecordPrograms.state, ports]
    simpa only [transfer, hl] using
      SubexpScanPrimitives.transfer_eval d0 21 12 0 1 (by decide) (by decide)
  have h2 : Eval (copy 16 11) (7 * (matrixBits p M).length + 5) d1 d2 := by
    have h := SubexpScanPrimitives.copy_eval d1 16 11 23 0 1
      (by decide) (by decide) (by decide) (by decide)
      (by simp [d1, d0, afterTransfer, StackRoutines.transferStacks,
        RecordPrograms.state, ports, stored])
    have hl : (d1.stacks 16).length = (matrixBits p M).length := by
      simp [d1, d0, afterTransfer, StackRoutines.transferStacks, RecordPrograms.state, ports, stored]
    simpa only [copy, hl] using h
  have h3 : Eval (copy 17 15) (7 * m + 5) d2 d3 := by
    have h := SubexpScanPrimitives.copy_eval d2 17 15 23 0 1
      (by decide) (by decide) (by decide) (by decide)
      (by simp [d2, d1, d0, afterCopy, afterTransfer, StackRoutines.copyStacks,
        StackRoutines.transferStacks, RecordPrograms.state, ports, stored])
    have hl : (d2.stacks 17).length = m := by
      simp [d2, d1, d0, afterCopy, afterTransfer, StackRoutines.copyStacks,
        StackRoutines.transferStacks, RecordPrograms.state, ports, stored]
    simpa only [copy, hl] using h
  have hentry : matrixView d3 = MatrixScalarProgram.state (d3.regs ∘ matrixRegs)
      [] [] (modulus p) [] [] (matrixBits p M) bits [] (zero p) (List.replicate m true) := by
    apply state_ext
    · rfl
    · funext j
      fin_cases j <;>
        simp [matrixView, matrixStacks, Function.comp_def, d3, d2, d1, d0, afterCopy,
          afterTransfer, StackRoutines.copyStacks, StackRoutines.transferStacks,
          RecordPrograms.state, ports, stored,
          MatrixScalarProgram.scalarStacks]
  obtain ⟨tm, htm, rm, hm⟩ := matrix_eval p M v d3 hentry
  let result := vectorWords p (BlockSearch.matrixMap M v)
  let d4 := withMatrix d3 (MatrixScalarProgram.state rm [] [] (modulus p)
    (MatrixProgramSupport.words result) [] [] bits [] (zero p) [])
  let d5 := afterCopy d4 17 15 0 1
  let d6 := flattened d5 result.flatten
  let d7 := cleared d6 12
  let d8 := emitted d7
  let d9 := restored d8
  have h5 : Eval (copy 17 15) (7 * m + 5) d4 d5 := by
    have h := SubexpScanPrimitives.copy_eval d4 17 15 23 0 1
      (by decide) (by decide) (by decide) (by decide)
      (by simp [d4, withMatrix, d3, d2, d1, d0, afterCopy, afterTransfer,
        StackRoutines.copyStacks, StackRoutines.transferStacks, RecordPrograms.state, ports, stored])
    have hl : (d4.stacks 17).length = m := by
      simp [d4, withMatrix, d3, d2, d1, d0, afterCopy, afterTransfer,
        StackRoutines.copyStacks, StackRoutines.transferStacks, RecordPrograms.state, ports, stored]
    simpa only [copy, hl] using h
  have hresultLength : result.length = m := vectorWords_length p _
  have hresultVolume : (result.map List.length).sum = m * width p := by
    simp [result, vectorWords, List.map_ofFn, Function.comp_def]
  have hresultFlat : result.flatten.length = m * width p := by
    rw [List.length_flatten, hresultVolume]
  have h6 : Eval flatten (9 * (m * width p) + 6 * m + 7) d5 d6 := by
    have h := flatten_eval d5 result
      (by simp [d5, d4, afterCopy, StackRoutines.copyStacks, withMatrix,
        MatrixScalarProgram.scalarStacks])
      (by simp [d5, d4, afterCopy, StackRoutines.copyStacks, withMatrix,
        MatrixScalarProgram.scalarStacks])
      (by simp [d5, d4, afterCopy, StackRoutines.copyStacks, withMatrix,
        MatrixScalarProgram.scalarStacks])
      (by simp [d5, d4, afterCopy, StackRoutines.copyStacks, withMatrix,
        MatrixScalarProgram.scalarStacks, hresultLength,
        d3, d2, d1, d0, afterTransfer, StackRoutines.transferStacks,
        RecordPrograms.state, ports, stored])
    simpa only [hresultVolume, hresultLength] using h
  have h7 : Eval (clear 12) (2 * bits.length + 3) d6 d7 := by
    have hl : (d6.stacks 12).length = bits.length := by
      simp [d6, flattened, d5, afterCopy, StackRoutines.copyStacks, d4,
        withMatrix, MatrixScalarProgram.scalarStacks]
    simpa only [hl] using clear_eval d6 12
  have h8 : Eval emit (8 * (m * width p) + 10) d7 d8 := by
    have h := emit_eval d7 (by
      simp [d7, cleared, d6, flattened, d5, afterCopy, StackRoutines.copyStacks, d4,
        withMatrix, d3, d2, d1, d0, afterTransfer, StackRoutines.transferStacks,
        RecordPrograms.state, ports, stored])
    have hl : (d7.stacks 10).length = m * width p := by
      simp [d7, cleared, d6, flattened, hresultFlat]
    simpa only [hl] using h
  have h9 : Eval restore 3 d8 d9 := restore_eval d8
  have hfinal : d9 = RecordPrograms.state ports
      (stored p M d9.regs [] [] (TupleProgram.prependRecord (bank p M v) output))
      false true false tail [] := by
    apply state_ext
    · funext j
      by_cases h10 : j = 10 <;> by_cases h11 : j = 11 <;> by_cases h12 : j = 12 <;>
        simp [d9, restored, RecordPrograms.state, ports, stored, h10, h11, h12]
    · exact callback_final_stacks p M regs rm bits result tail output
  have he := h1.seq (h2.seq (h3.seq (hm.seq (h5.seq (h6.seq (h7.seq (h8.seq h9)))))))
  rw [hfinal] at he
  refine ⟨_, ?_, d9.regs, he⟩
  change _ ≤ callbackBudget p M bits
  unfold callbackBudget
  omega

def imageBits (p : ℕ) [Fact p.Prime] {m n : ℕ} (M : Fin m → Fin n → ZMod p) (bits : List Bool) :=
  bank p M (decode p n bits)

def invariant (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (d : Data) : Prop :=
  ∃ regs output, d = stored p M regs [] [] output

def validPayload (p n : ℕ) (bits : List Bool) : Prop :=
  ∃ v : Fin n → ZMod p, bits = MatrixProgramSupport.words (vectorWords p v)

theorem callback_contract (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) :
    RecordPrograms.CallbackContractWithOn ports callback (fun _ => false)
      (callbackBudget p M) (invariant p M)
      (fun bits a b => b.stacks 22 = TupleProgram.prependRecord (imageBits p M bits) (a.stacks 22))
      (validPayload p n) := by
  rintro bits tail base ⟨v, rfl⟩ ⟨regs, output, rfl⟩
  obtain ⟨t, ht, rf, he⟩ := callback_eval p M v regs tail output
  refine ⟨t, stored p M rf [] [] (TupleProgram.prependRecord (bank p M v) output),
    ht, ⟨rf, _, rfl⟩, ?_, he⟩
  simp [stored, imageBits, decode_words]

abbrev iterate : Cmd 13 32 := RecordPrograms.iterate ports callback

theorem iterate_eval (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (regs : Fin 13 → Bool) :
    ∃ t ≤ 3 + RecordPrograms.budget (callbackBudget p M) (coefficientRows p n), ∃ rf,
      Eval iterate t
        (stored p M regs (ProgramEncoding.encodeRecords (coefficientRows p n)) []
          (ProgramEncoding.encodeRecords []))
        (stored p M rf [] [] (ProgramEncoding.encodeRecords (bankRecords p M))) := by
  let base := stored p M regs [] [] (ProgramEncoding.encodeRecords [])
  have hv : ∀ bits ∈ coefficientRows p n, validPayload p n bits := by
    intro bits hbits
    exact ⟨decode p n bits, (coefficientRows_valid p n bits hbits).symm⟩
  obtain ⟨t, next, ht, hnext, history, he⟩ := RecordPrograms.iterate_run_with_on
    ports callback (fun _ => false) (callbackBudget p M) (invariant p M)
    (fun bits a b => b.stacks 22 = TupleProgram.prependRecord (imageBits p M bits) (a.stacks 22))
    (validPayload p n) (callback_contract p M) (coefficientRows p n) [] base hv
    ⟨regs, _, rfl⟩ (regs 10) (regs 11) (regs 12)
  obtain ⟨rf, output, rfl⟩ := hnext
  have hout := history.fold_of_false (by simp) (fun d => d.stacks 22)
    (fun acc bits => TupleProgram.prependRecord (imageBits p M bits) acc) (fun _ _ _ h => h)
  change output = (coefficientRows p n).foldl
    (fun acc bits => TupleProgram.prependRecord (imageBits p M bits) acc)
    (ProgramEncoding.encodeRecords []) at hout
  rw [← List.foldl_map (f := imageBits p M) (g := fun acc bits => TupleProgram.prependRecord bits acc),
    TupleProgram.fold_prependRecord, TupleProgram.appendEncoded_encodeRecords] at hout
  have hmap : ((coefficientRows p n).map (imageBits p M)).reverse = bankRecords p M := by
    simp only [bankRecords, coefficients, List.map_map, Function.comp_def]
    rfl
  simp only [List.append_nil, hmap] at hout
  subst output
  have hstart : RecordPrograms.state ports base (regs 10) (regs 11) (regs 12)
      (Encoding.encodeList id (coefficientRows p n) ++ []) [] =
      stored p M regs (ProgramEncoding.encodeRecords (coefficientRows p n)) []
        (ProgramEncoding.encodeRecords []) := by
    apply state_ext
    · funext j
      by_cases h10 : j = 10 <;> by_cases h11 : j = 11 <;> by_cases h12 : j = 12 <;>
        simp [RecordPrograms.state, ports, base, stored, h10, h11, h12]
    · funext j
      fin_cases j <;> simp [RecordPrograms.state, ports, base, stored, ProgramEncoding.encodeRecords]
  have hany : (coefficientRows p n).any (fun _ => false) = false := by simp
  have hunread : RecordPrograms.unread (fun _ => false) (coefficientRows p n) [] = [] :=
    TupleProgram.unread_false _ _
  rw [hstart, hany, hunread] at he
  let finish := RecordPrograms.state ports
    (stored p M rf [] [] (ProgramEncoding.encodeRecords (bankRecords p M))) false true false [] []
  have hfinish : finish = stored p M finish.regs [] []
      (ProgramEncoding.encodeRecords (bankRecords p M)) := by
    apply state_ext
    · rfl
    · funext j; fin_cases j <;> simp [finish, RecordPrograms.state, ports, stored]
  change Eval iterate t
    (stored p M regs (ProgramEncoding.encodeRecords (coefficientRows p n)) []
      (ProgramEncoding.encodeRecords [])) finish at he
  rw [hfinish] at he
  exact ⟨t, ht, finish.regs, he⟩

def generatorRegs : Fin 10 → Fin 13 := Fin.castAdd 3
def generatorStacks : Fin 9 → Fin 32 := ![20, 18, 24, 25, 26, 27, 28, 29, 30]
theorem generatorRegs_injective : Function.Injective generatorRegs := Fin.castAdd_injective _ _
theorem generatorStacks_injective : Function.Injective generatorStacks := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [generatorStacks]

abbrev generate : Cmd 13 32 := .seq (copy 19 30)
  (.seq (.call (ProgramLinking.liftProgram TupleProgram.generateProgram generatorRegs generatorStacks))
    (.seq (clear 27) (TupleProgram.pushConst 22 0 false)))

theorem generate_eval (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (regs : Fin 13 → Bool) :
    ∃ t ≤ 7 * n + TupleProgram.powerCost (tokens p) n [[]] + 21, ∃ rf,
      Eval generate t (stored p M regs [] [] [])
        (stored p M rf (ProgramEncoding.encodeRecords (coefficientRows p n)) []
          (ProgramEncoding.encodeRecords [])) := by
  let d0 := stored p M regs [] [] []
  let d1 := afterCopy d0 19 30 0 1
  let a : State 10 9 := ⟨d1.regs ∘ generatorRegs, d1.stacks ∘ generatorStacks⟩
  have h1 : Eval (copy 19 30) (7 * n + 5) d0 d1 := by
    have hl : (d0.stacks 19).length = n := by simp [d0, stored]
    simpa only [copy, hl] using SubexpScanPrimitives.copy_eval d0 19 30 23 0 1
      (by decide) (by decide) (by decide) (by decide) (by simp [d0, stored])
  have ha : TupleProgram.outerInvariant (tokens p) (List.replicate n true) (a.regs 9) a := by
    simp [TupleProgram.outerInvariant, a, generatorStacks,
      d1, afterCopy, StackRoutines.copyStacks, d0, stored]
  obtain ⟨b, hb, t, ht, htrace⟩ := TupleProgram.generateProgram_runsIn
    (tokens p) (List.replicate n true) (a.regs 9) a ha
    (by simp [a, generatorStacks, d1, afterCopy, StackRoutines.copyStacks, d0, stored])
    (by simp [a, generatorStacks, d1, afterCopy, StackRoutines.copyStacks, d0, stored])
    (by simp [a, generatorStacks, d1, afterCopy, StackRoutines.copyStacks, d0, stored])
  simp only [List.length_replicate] at hb ht
  let d2 := embedState generatorRegs generatorStacks d1 b
  have hin : embedState generatorRegs generatorStacks d1 a = d1 := by
    apply embedState_eq _ _ generatorRegs_injective generatorStacks_injective
    · intro i; rfl
    · intro i; rfl
    · intros; rfl
    · intros; rfl
  have h2 : Eval (.call
      (ProgramLinking.liftProgram TupleProgram.generateProgram generatorRegs generatorStacks)) t d1 d2 := by
    have he := eval_call_lifted TupleProgram.generateProgram generatorRegs generatorStacks d1
      generatorRegs_injective generatorStacks_injective htrace
    change Eval (.call
      (ProgramLinking.liftProgram TupleProgram.generateProgram generatorRegs generatorStacks)) t
      (embedState generatorRegs generatorStacks d1 a) d2 at he
    rw [hin] at he
    exact he
  rcases hb with ⟨⟨hb1, hb3, hb4, hb6, hb7, hb8, hb9⟩, hb0, hb2, hb5⟩
  have hshape : d2.stacks = Function.update
      (stored p M d2.regs (ProgramEncoding.encodeRecords (coefficientRows p n)) [] []).stacks
      27 [false] := by
    funext j
    by_cases hj : ∃ i, generatorStacks i = j
    · obtain ⟨i, rfl⟩ := hj
      change (embedState generatorRegs generatorStacks d1 b).stacks (generatorStacks i) = _
      rw [embedState_stack _ _ _ _ generatorStacks_injective]
      fin_cases i <;>
        simp [generatorStacks, stored, coefficientRows, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8]
    · change (embedState generatorRegs generatorStacks d1 b).stacks j = _
      rw [embedState_stack_frame _ _ _ _ j hj]
      have h20 : j ≠ 20 := fun h => hj ⟨0, by simpa [generatorStacks] using h.symm⟩
      have h27 : j ≠ 27 := fun h => hj ⟨5, by simpa [generatorStacks] using h.symm⟩
      have h30 : j ≠ 30 := fun h => hj ⟨8, by simpa [generatorStacks] using h.symm⟩
      simp [d1, afterCopy, StackRoutines.copyStacks, d0, stored, h20, h27, h30]
  let d3 := cleared d2 27
  let d4 := TupleProgram.pushedState 22 0 false d3
  have h3 : Eval (clear 27) 5 d2 d3 := by
    have he := clear_eval d2 27
    have hl : (d2.stacks 27).length = 1 := by simp [hshape]
    simpa only [hl] using he
  have h4 := TupleProgram.pushConst_eval 22 (0 : Fin 13) false d3
  have hfinal : d4 = stored p M d4.regs (ProgramEncoding.encodeRecords (coefficientRows p n)) []
      (ProgramEncoding.encodeRecords []) := by
    apply state_ext
    · rfl
    · funext j
      simp only [d4, d3, cleared, hshape]
      fin_cases j <;> simp [stored, ProgramEncoding.encodeRecords, Encoding.encodeList]
  change Eval (TupleProgram.pushConst 22 0 false) 2 d3 d4 at h4
  rw [hfinal] at h4
  refine ⟨(7 * n + 5) + (t + (5 + 2)), by omega, d4.regs, ?_⟩
  exact h1.seq (h2.seq (h3.seq h4))

abbrev command : Cmd 13 32 := .seq generate iterate
def program := compiled command 16 22

def sourceBudget (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) : ℕ :=
  7 * n + TupleProgram.powerCost (tokens p) n [[]] + 25 +
    RecordPrograms.budget (callbackBudget p M) (coefficientRows p n)

/-- The full fixed program constructs all image-vector records from scalar
tokens and the runtime matrix. No vector list or vector-call trace is an input. -/
theorem program_run (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (regs : Fin 13 → Bool) :
    ∃ rf, RunsIn program (sourceBudget p M)
      ((stored p M regs [] [] []).withPC (some program.entry))
      ((stored p M rf [] [] (ProgramEncoding.encodeRecords (bankRecords p M))).withPC none) := by
  obtain ⟨a, ha, ra, ea⟩ := generate_eval p M regs
  obtain ⟨b, hb, rb, eb⟩ := iterate_eval p M ra
  refine ⟨rb, a + b + 1, ?_, ?_⟩
  · unfold sourceBudget
    omega
  · exact compiled_halt_trace (ea.seq eb) 16 22

theorem primitive_run (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) (regs : Fin 13 → Bool) :
    ∃ rf, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * sourceBudget p M)
      (primitiveCfg program ((stored p M regs [] [] []).withPC (some program.entry)))
      (primitiveCfg program
        ((stored p M rf [] [] (ProgramEncoding.encodeRecords (bankRecords p M))).withPC none)) := by
  obtain ⟨rf, hr⟩ := program_run p M regs
  exact ⟨rf, primitive_execution program hr⟩

theorem bankRecords_length (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) : (bankRecords p M).length = p ^ n := by
  simp [bankRecords, coefficients_length]

theorem output_length (p : ℕ) [Fact p.Prime] {m n : ℕ}
    (M : Fin m → Fin n → ZMod p) :
    (ProgramEncoding.encodeRecords (bankRecords p M)).length =
      1 + (2 * (m * width p) + 2) * p ^ n := by
  rw [ProgramEncoding.encodeRecords_length]
  have hv : ((bankRecords p M).map List.length).sum = p ^ n * (m * width p) := by
    simp [bankRecords, List.map_reverse, List.map_map,
      Function.comp_def, bank_length, coefficients_length]
  rw [hv, bankRecords_length]
  ring

end SubexponentialSAT.Subexp.MatrixImageEnumeration

end OAI.Algorithms
