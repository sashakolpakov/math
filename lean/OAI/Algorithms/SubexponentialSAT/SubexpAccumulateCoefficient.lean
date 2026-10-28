import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCoefficientLookup
import OAI.Algorithms.SubexponentialSAT.SubexpJetCellProgram

namespace OAI.Algorithms

/-!
# Concrete coefficient lookup and jet accumulation

Move the saved reversed query to the scanner, run the actual coefficient
lookup, and update one packed jet cell with actual quartic addition. Cleanup
clears the consumed index and query and restores the outer iterator flags.
-/

namespace SubexponentialSAT.SubexpAccumulateCoefficient

open BitProgram StructuredCalls SubexpScanPrimitives
open SubexpLiftRing SubexpQuarticRing
open SubexpJetCellProgram (regPorts scalarPorts regPorts_injective scalarPorts_injective)

abbrev Data := State 16 128
abbrev Code := Cmd 16 128

def lookupCall : Code := .call
  (ProgramLinking.liftProgram SubexpCoefficientLookup.lookupProgram regPorts scalarPorts)

def lookupOut (d : Data) (regs : Fin 8 → Bool) (value : List Bool) : Data :=
  ⟨Fin.addCases (m := 8) (n := 8) (motive := fun _ => Bool) regs (fun i => d.regs (Fin.natAdd 8 i)),
    Function.update (Function.update d.stacks 8 value) 15 []⟩

theorem lookupOut_small (d : Data) (regs : Fin 8 → Bool)
    (modulus value width query source : List Bool)
    (hsmall : ∀ i : Fin 20, d.stacks (scalarPorts i) =
      (SubexpCoefficientLookup.state (d.regs ∘ regPorts) modulus [] [] width query source []).stacks i) :
    ∀ i : Fin 20, (lookupOut d regs value).stacks (scalarPorts i) =
      (SubexpCoefficientLookup.state regs modulus value [] width query [] []).stacks i := by
  intro i
  have hi := hsmall i
  fin_cases i <;>
    simp [lookupOut, scalarPorts, SubexpCoefficientLookup.state, SubexpCoefficientLookup.frame,
      SubexpFlatAdd.ready, SubexpFlatAdd.state, SubexpFlatAdd.stacks,
      Fin.addCases, Fin.coe_ofNat_eq_mod] at hi ⊢ <;> exact hi

def resetFlags : Code :=
  .seq (RecordPrograms.atom (.set 13 false))
    (.seq (RecordPrograms.atom (.set 14 true)) (RecordPrograms.atom (.set 15 false)))

def resetState (d : Data) : Data :=
  ⟨Function.update (Function.update (Function.update d.regs 13 false) 14 true) 15 false, d.stacks⟩

theorem resetFlags_eval (d : Data) : Eval resetFlags 3 d (resetState d) := by
  have h₀ := Eval.base (StructuredProgram.Eval.atom (.set (13 : Fin 16) false) d)
  have h₁ := Eval.base (StructuredProgram.Eval.atom (.set (14 : Fin 16) true)
    ((StructuredProgram.Atom.set 13 false).eval d))
  have h₂ := Eval.base (StructuredProgram.Eval.atom (.set (15 : Fin 16) false)
    ((StructuredProgram.Atom.set 14 true).eval ((StructuredProgram.Atom.set 13 false).eval d)))
  simpa [resetFlags, resetState, RecordPrograms.atom, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, StructuredProgram.State.withPC,
    execInstr] using Eval.seq h₀ (Eval.seq h₁ h₂)

/-- The scanner and updater are concrete finite instruction tables. -/
def code : Code :=
  .seq (SubexpJetCellProgram.moveForward 105 14)
    (.seq lookupCall (.seq SubexpJetCellProgram.updateCell
      (.seq (SubexpJetCellProgram.clear 103)
        (.seq (SubexpJetCellProgram.clear 14) resetFlags))))

abbrev program : Program 16 128 (StructuredCalls.size code + 1) :=
  StructuredCalls.compiled code 15 102

def lookupBudget (B : ℕ) (query : List Bool) (records : List (List Bool)) : ℕ :=
  14 * B + 12 + RecordPrograms.budget (SubexpCoefficientLookup.recordCost B query) records

def budget (B I : ℕ) (query : List Bool) (records : List (List Bool)) : ℕ :=
  14 * B + RecordPrograms.budget (SubexpCoefficientLookup.recordCost B query) records +
    SubexpJetCellProgram.eventBudget B I + 8 * query.length + 2 * I + 27

/-- Net effect: clear consumed data and replace the selected jet cell. -/
def resultStacks (stk : Fin 128 → List Bool) (jet : List Bool) : Fin 128 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update stk 105 []) 15 []) 8 []) 102 jet) 103 []) 14 []

theorem resultStacks_high (stk : Fin 128 → List Bool) (jet : List Bool)
    (j : Fin 128) (hj : 100 ≤ j.val) (h102 : j ≠ 102) (h103 : j ≠ 103) (h105 : j ≠ 105) :
    resultStacks stk jet j = stk j := by
  have h8 : j ≠ 8 := by intro h; subst j; norm_num [Fin.coe_ofNat_eq_mod] at hj
  have h14 : j ≠ 14 := by intro h; subst j; norm_num [Fin.coe_ofNat_eq_mod] at hj
  have h15 : j ≠ 15 := by intro h; subst j; norm_num [Fin.coe_ofNat_eq_mod] at hj
  simp [resultStacks, h8, h14, h15, h102, h103, h105]

/-- Cleanup restores the scanner workspace for the next extraction job. -/
theorem resultStacks_small (d : Data) (modulus width source jet : List Bool)
    (hsmall : ∀ i : Fin 20, d.stacks (scalarPorts i) =
      (SubexpCoefficientLookup.state (d.regs ∘ regPorts) modulus [] [] width [] source []).stacks i) :
    ∀ i : Fin 20, resultStacks d.stacks jet (scalarPorts i) =
      (SubexpCoefficientLookup.state (d.regs ∘ regPorts) modulus [] [] width [] [] []).stacks i := by
  intro i
  have hi := hsmall i
  fin_cases i <;>
    simp [resultStacks, scalarPorts, SubexpCoefficientLookup.state,
      SubexpCoefficientLookup.frame, SubexpFlatAdd.ready, SubexpFlatAdd.state,
      SubexpFlatAdd.stacks, Fin.addCases, Fin.coe_ofNat_eq_mod] at hi ⊢ <;> exact hi

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

/-- Lift the actual scanner trace into the shared machine. -/
theorem lookupCall_eval (d : Data) (records : List (SubexpCoefficientLookup.Record p μ))
    (width query : List Bool) (hwidth : width.length = baseWidth p μ)
    (hsmall : ∀ i : Fin 20, d.stacks (scalarPorts i) =
      (SubexpCoefficientLookup.state (d.regs ∘ regPorts) M.bits [] [] width query
        (Encoding.encodeList id (SubexpCoefficientLookup.encoded p μ records)) []).stacks i) :
    ∃ n ≤ lookupBudget (baseWidth p μ) query (SubexpCoefficientLookup.encoded p μ records),
      ∃ regs', Eval lookupCall n d
        (lookupOut d (SubexpCoefficientLookup.normalized regs' false true false)
          (SubexpFlatAdd.encode (SubexpCoefficientLookup.fold p μ M query
            (SubexpCoefficientLookup.zeroCoefficient p μ) records))) := by
  obtain ⟨regs', n, hn, ht⟩ := SubexpCoefficientLookup.lookup_runs p μ M
    (d.regs ∘ regPorts) records width query [] hwidth
  let left := SubexpCoefficientLookup.state (d.regs ∘ regPorts) M.bits [] [] width query
    (Encoding.encodeList id (SubexpCoefficientLookup.encoded p μ records)) []
  let value := SubexpFlatAdd.encode (SubexpCoefficientLookup.fold p μ M query
    (SubexpCoefficientLookup.zeroCoefficient p μ) records)
  let regsOut := SubexpCoefficientLookup.normalized regs' false true false
  let right := SubexpCoefficientLookup.state regsOut M.bits value [] width query [] []
  have hl : embedState regPorts scalarPorts d left = d := by
    apply embedState_eq _ _ regPorts_injective scalarPorts_injective
    · intros; rfl
    · exact hsmall
    · intros; rfl
    · intros; rfl
  have hr : embedState regPorts scalarPorts d right = lookupOut d regsOut value := by
    apply embedState_eq _ _ regPorts_injective scalarPorts_injective
    · intro i
      simp [lookupOut, right, SubexpCoefficientLookup.state, SubexpFlatAdd.ready,
        SubexpFlatAdd.state, regPorts]
    · exact lookupOut_small d regsOut M.bits value width query _ hsmall
    · intro j
      refine Fin.addCases (m := 8) (n := 8) ?_ ?_ j
      · intro i hi
        exact False.elim (hi ⟨i, rfl⟩)
      · intro i _
        simp [lookupOut, Fin.addCases_right, -Fin.natAdd_eq_addNat]
    · intro j hj
      have h8 : j ≠ 8 := fun h => hj ⟨8, by simpa [scalarPorts] using h.symm⟩
      have h15 : j ≠ 15 := fun h => hj ⟨15, by simpa [scalarPorts] using h.symm⟩
      simp [lookupOut, h8, h15]
  have ht' : Trace SubexpCoefficientLookup.lookupProgram n
      (left.withPC (some SubexpCoefficientLookup.lookupProgram.entry)) (right.withPC none) := by
    simpa only [left, right, value, regsOut, List.append_nil] using ht
  have he := eval_call_lifted SubexpCoefficientLookup.lookupProgram regPorts scalarPorts d
    regPorts_injective scalarPorts_injective ht'
  refine ⟨n, hn, regs', ?_⟩
  simpa only [hl, hr, lookupCall] using he

/-- Exact typed-array update, followed by cleanup and iterator-flag reset.
The parser stores the reversed query on 105, which is moved unchanged to 14. -/
theorem accumulate_eval (d : Data) (records : List (SubexpCoefficientLookup.Record p μ))
    (query : List Bool) (old : SubexpCoefficientLookup.Coefficient p μ)
    (earlierCells suffix : List (SubexpCoefficientLookup.Coefficient p μ))
    (indexWord widthWord scalarWidth : List Bool)
    (hquery : d.stacks 105 = query.reverse)
    (hjet : d.stacks 102 = ((earlierCells ++ old :: suffix).map SubexpFlatAdd.encode).flatten)
    (hindex : d.stacks 103 = indexWord) (hindexLen : indexWord.length = earlierCells.length)
    (hwidth : d.stacks 104 = widthWord) (hwidthLen : widthWord.length = 4 * baseWidth p μ)
    (hscalarWidth : scalarWidth.length = baseWidth p μ)
    (hsmall : ∀ i : Fin 20, d.stacks (scalarPorts i) =
      (SubexpCoefficientLookup.state (d.regs ∘ regPorts) M.bits [] [] scalarWidth []
        (Encoding.encodeList id (SubexpCoefficientLookup.encoded p μ records)) []).stacks i)
    (h112 : d.stacks 112 = []) (h113 : d.stacks 113 = [])
    (h114 : d.stacks 114 = []) (h115 : d.stacks 115 = [])
    (h116 : d.stacks 116 = []) (h117 : d.stacks 117 = []) (h118 : d.stacks 118 = []) :
    ∃ n ≤ budget (baseWidth p μ) indexWord.length query (SubexpCoefficientLookup.encoded p μ records),
      ∃ e : Data, Eval code n d e ∧
        e.stacks = resultStacks d.stacks
          (((earlierCells ++ (SubexpPreparedQuartic.binaryAdd p μ M
              (SubexpCoefficientLookup.fold p μ M query
                (SubexpCoefficientLookup.zeroCoefficient p μ) records) old).1 :: suffix).map
            SubexpFlatAdd.encode).flatten) ∧
        e.regs 13 = false ∧ e.regs 14 = true ∧ e.regs 15 = false := by
  let contribution := SubexpCoefficientLookup.fold p μ M query
    (SubexpCoefficientLookup.zeroCoefficient p μ) records
  let d₁ := SubexpJetCellProgram.moveOut d 105 14
  have h₁ := SubexpJetCellProgram.moveForward_eval d 105 14
    (by decide) (by decide) (by decide) h118
  have h14 : d.stacks 14 = [] := by
    simpa [scalarPorts, SubexpCoefficientLookup.state, SubexpCoefficientLookup.frame,
      SubexpFlatAdd.ready, SubexpFlatAdd.state, SubexpFlatAdd.stacks,
      Fin.addCases, Fin.coe_ofNat_eq_mod] using hsmall 14
  have hsmall₁ : ∀ i : Fin 20, d₁.stacks (scalarPorts i) =
      (SubexpCoefficientLookup.state (d₁.regs ∘ regPorts) M.bits [] [] scalarWidth query
        (Encoding.encodeList id (SubexpCoefficientLookup.encoded p μ records)) []).stacks i := by
    intro i
    have hi := hsmall i
    fin_cases i <;>
      simp [d₁, SubexpJetCellProgram.moveOut, scalarPorts, SubexpCoefficientLookup.state,
        SubexpCoefficientLookup.frame, SubexpFlatAdd.ready, SubexpFlatAdd.state,
        SubexpFlatAdd.stacks, Fin.addCases, Fin.coe_ofNat_eq_mod, hquery, h14] at hi ⊢ <;> exact hi
  obtain ⟨n, hn, regs', h₂⟩ := lookupCall_eval p μ M d₁ records scalarWidth query hscalarWidth hsmall₁
  let d₂ := lookupOut d₁ (SubexpCoefficientLookup.normalized regs' false true false)
    (SubexpFlatAdd.encode contribution)
  have hsmall₂ : ∀ i : Fin 20, d₂.stacks (scalarPorts i) =
      (SubexpFlatAdd.ready (d₂.regs ∘ regPorts) M.bits (SubexpFlatAdd.encode contribution)
        [] scalarWidth [] (SubexpCoefficientLookup.frame query [] [])).stacks i := by
    exact lookupOut_small d₁ _ M.bits (SubexpFlatAdd.encode contribution) scalarWidth query _ hsmall₁
  obtain ⟨m, hm, d₃, h₃, hst, _⟩ := SubexpJetCellProgram.updateCell_typed_eval p μ M d₂
    contribution old earlierCells suffix widthWord indexWord scalarWidth
    (SubexpCoefficientLookup.frame query [] [])
    (by simpa [d₂, d₁, lookupOut, SubexpJetCellProgram.moveOut] using hjet)
    (by simpa [d₂, d₁, lookupOut, SubexpJetCellProgram.moveOut] using hindex) hindexLen
    (by simpa [d₂, d₁, lookupOut, SubexpJetCellProgram.moveOut] using hwidth) hwidthLen
    hscalarWidth hsmall₂
    (by simpa [d₂, d₁, lookupOut, SubexpJetCellProgram.moveOut] using h112)
    (by simpa [d₂, d₁, lookupOut, SubexpJetCellProgram.moveOut] using h113)
    (by simpa [d₂, d₁, lookupOut, SubexpJetCellProgram.moveOut] using h114)
    (by simpa [d₂, d₁, lookupOut, SubexpJetCellProgram.moveOut] using h115)
    (by simpa [d₂, d₁, lookupOut, SubexpJetCellProgram.moveOut] using h116)
    (by simpa [d₂, d₁, lookupOut, SubexpJetCellProgram.moveOut] using h117)
    (by simpa [d₂, d₁, lookupOut, SubexpJetCellProgram.moveOut] using h118)
  let d₄ := SubexpJetCellProgram.clearOut d₃ 103
  let d₅ := SubexpJetCellProgram.clearOut d₄ 14
  let d₆ := resetState d₅
  have h₄ := SubexpJetCellProgram.clear_eval d₃ 103
  have h₅ := SubexpJetCellProgram.clear_eval d₄ 14
  have h₆ := resetFlags_eval d₅
  have ht : Eval code _ d d₆ := Eval.seq h₁ (Eval.seq h₂ (Eval.seq h₃
    (Eval.seq h₄ (Eval.seq h₅ h₆))))
  have hlen105 : (d.stacks 105).length = query.length := by simp [hquery]
  have hlen103 : (d₃.stacks 103).length = indexWord.length := by
    simp [hst, d₂, d₁, lookupOut, SubexpJetCellProgram.moveOut, hindex]
  have hlen14 : (d₄.stacks 14).length = query.length := by
    simp [d₄, hst, d₂, d₁, lookupOut, SubexpJetCellProgram.clearOut,
      SubexpJetCellProgram.moveOut, hquery, h14]
  refine ⟨_, ?_, d₆, ht, ?_, ?_, ?_, ?_⟩
  · rw [hlen105, hlen103, hlen14]
    unfold lookupBudget at hn
    unfold budget
    omega
  · change d₅.stacks = _
    simp only [d₅, d₄, SubexpJetCellProgram.clearOut, hst]
    funext j
    by_cases h14j : j = 14
    · subst j; simp [resultStacks]
    by_cases h103j : j = 103
    · subst j; simp [resultStacks]
    by_cases h102j : j = 102
    · subst j; simp [resultStacks, contribution]
    by_cases h8j : j = 8
    · subst j; simp [resultStacks]
    by_cases h15j : j = 15
    · subst j; simp [resultStacks, d₂, lookupOut]
    by_cases h105j : j = 105
    · subst j; simp [resultStacks, d₂, d₁, lookupOut, SubexpJetCellProgram.moveOut]
    simp [resultStacks, d₂, d₁, lookupOut, SubexpJetCellProgram.moveOut,
      h14j, h103j, h102j, h8j, h15j, h105j]
  · simp [d₆, resetState]
  · simp [d₆, resetState]
  · simp [d₆, resetState]

/-- The compiled suffix includes a real final halt instruction. -/
theorem program_trace {n : ℕ} {d e : Data} (h : Eval code n d e) :
    Trace program (n + 1) (d.withPC (some program.entry)) (e.withPC none) :=
  StructuredCalls.compiled_halt_trace h 15 102

theorem program_runs {n bound : ℕ} {d e : Data} (h : Eval code n d e) (hn : n ≤ bound) :
    RunsIn program (bound + 1) (d.withPC (some program.entry)) (e.withPC none) :=
  ⟨n + 1, Nat.add_le_add_right hn 1, program_trace h⟩

theorem result_caller_frame {d e : Data} {jet : List Bool}
    (h : e.stacks = resultStacks d.stacks jet) (j : Fin 128) (hj : 100 ≤ j.val)
    (h102 : j ≠ 102) (h103 : j ≠ 103) (h105 : j ≠ 105) : e.stacks j = d.stacks j := by
  rw [h]
  exact resultStacks_high d.stacks jet j hj h102 h103 h105

theorem program_call {n : ℕ} {d e : Data} (h : Eval code n d e) :
    Eval (.call program) (n + 1) d e := Eval.call program (program_trace h)

/-- Polynomial in the serialized source, query, index, and scalar width. -/
theorem budget_le_input (B I : ℕ) (query : List Bool) (records : List (List Bool)) :
    budget B I query records + 1 ≤
      30000 * (I + 1) * (B + 1)^2 + 14 * B + 8 * query.length + 2 * I + 23 +
        (9 * query.length + 4 * SubexpFlatAdd.wordCost B + 48 * B + 75) *
          ((Encoding.encodeList id records).length + 1) := by
  have hs := SubexpCoefficientLookup.scan_budget_le_input B query records
  have he := SubexpJetCellProgram.eventBudget_polynomial B I
  unfold budget
  omega

/-- The updated stored cell denotes its old value plus every matching
coefficient in the evaluated record list, including duplicate keys. -/
theorem accumulated_quotient (c : Fin 4 → ZMod (p ^ μ)) (query : List Bool)
    (old : SubexpCoefficientLookup.Coefficient p μ)
    (records : List (SubexpCoefficientLookup.Record p μ)) :
    quotientDenote c (((SubexpPreparedQuartic.binaryAdd p μ M
      (SubexpCoefficientLookup.fold p μ M query
        (SubexpCoefficientLookup.zeroCoefficient p μ) records) old).1).map (wordValue p μ)) =
      quotientDenote c (old.map (wordValue p μ)) +
        (records.map (fun r => if r.1 = query then
          quotientDenote c (r.2.map (wordValue p μ)) else 0)).sum := by
  rw [SubexpPreparedQuartic.binaryAdd_quotient, SubexpCoefficientLookup.lookup_quotient]
  exact add_comm _ _

end SubexponentialSAT.SubexpAccumulateCoefficient

end OAI.Algorithms
