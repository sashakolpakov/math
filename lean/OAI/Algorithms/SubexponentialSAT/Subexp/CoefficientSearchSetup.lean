import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ScalarSetupProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearchGeneration
import OAI.Algorithms.SubexponentialSAT.Subexp.CoefficientSearchCallback

namespace OAI.Algorithms

/-!
# Concrete scalar preparation for coefficient search

A fixed lifted scalar-setup program consumes the binary prime word. Its
temporary raw alphabet is physically cleared before the coefficient search
starts. The unary interval inputs and all four caller-control registers are
preserved.
-/

namespace SubexponentialSAT.Subexp.CoefficientSearchSetup

open BitProgram StructuredCalls SubexpScanPrimitives MatrixWordEncoding
open BlockSearchPreparation (restrictState lifted_call)

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod
attribute [local simp] MatrixProgramSupport.words

abbrev Data := CoefficientSearchProgram.Data

def scalarRegisters (i : Fin 6) : Fin 14 := Fin.castAdd 8 i

def scalarStacks : Fin 9 → Fin 32 := ![14,26,27,28,29,20,25,19,5]

theorem scalarRegisters_injective : Function.Injective scalarRegisters :=
  Fin.castAdd_injective _ _

theorem scalarStacks_injective : Function.Injective scalarStacks := by decide

/-- Only the prime word and the two true-token counters are supplied. -/
def rawInput (p A R : ℕ) (regs : Fin 14 → Bool) : Data :=
  ⟨regs, fun i => if i = 14 then SubexpAlphabetProgram.primeWord p
    else if i = 16 then List.replicate R true
    else if i = 31 then List.replicate A true else []⟩

abbrev setup : Cmd 14 32 :=
  .seq (.call (ProgramLinking.liftProgram ScalarSetupProgram.program
    scalarRegisters scalarStacks)) (CoefficientSearchProgram.clear 20)

/-- Scalar setup may change its six local registers; the next two are a frame. -/
def lowRegisters (original : Fin 14 → Bool) (localRegs : Fin 6 → Bool) : Fin 8 → Bool :=
  Fin.addCases (m := 6) (n := 2) (motive := fun _ => Bool) localRegs ![original 6,original 7]

variable (p : ℕ) [Fact p.Prime]

def rawAlphabetEncoded : List Bool :=
  ProgramEncoding.encodeRecords (ScalarSetupProgram.rawAlphabet p)

def budget : ℕ := ScalarSetupProgram.budget p + 2 * (rawAlphabetEncoded p).length + 3

def middle (A R : ℕ) (original : Fin 14 → Bool) (localRegs : Fin 6 → Bool) : Data :=
  let ready := CoefficientSearchProgram.inputState p A R (lowRegisters original localRegs)
    (original 8) (original 9) (original 10) (original 11) (original 12) (original 13)
  ⟨ready.regs,Function.update ready.stacks 20 (rawAlphabetEncoded p)⟩

omit [Fact p.Prime] in
theorem restrict_rawInput (A R : ℕ) (regs : Fin 14 → Bool) :
    restrictState scalarRegisters scalarStacks (rawInput p A R regs) =
      ScalarSetupProgram.inputState p (regs ∘ scalarRegisters) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;>
      simp [scalarStacks, rawInput]

/-- The lifted scalar setup has exactly the physical layout expected by the
search, with one additional raw-alphabet buffer awaiting its clear. -/
theorem embed_output (A R : ℕ) (original : Fin 14 → Bool) (localRegs : Fin 6 → Bool) :
    embedState scalarRegisters scalarStacks (rawInput p A R original)
      (ScalarSetupProgram.outputState p localRegs) = middle p A R original localRegs := by
  apply embedState_eq_of_ports scalarRegisters scalarStacks
    (rawInput p A R original) _ (ScalarSetupProgram.outputState p localRegs)
    scalarRegisters_injective scalarStacks_injective
  · intro i
    fin_cases i <;>
      simp [middle,lowRegisters,scalarRegisters,ScalarSetupProgram.outputState,
        ScalarSetupProgram.state,CoefficientSearchProgram.inputState,
        CoefficientSearchProgram.generationInput,CoefficientSearchProgram.wide,
        CoefficientSearchProgram.blank,CoefficientCheckerProgram.wide,
        CoefficientCheckerProgram.lowData,MatrixScalarProgram.state]
  · intro i hi
    have hi6 : 6 ≤ i.val := by
      by_contra h
      exact hi ⟨⟨i.val,by omega⟩,Fin.ext rfl⟩
    fin_cases i <;>
      simp_all [middle,lowRegisters,scalarRegisters,rawInput,
        CoefficientSearchProgram.inputState,CoefficientSearchProgram.generationInput,
        CoefficientSearchProgram.wide,CoefficientSearchProgram.blank,
        CoefficientCheckerProgram.wide,CoefficientCheckerProgram.lowData,
        MatrixScalarProgram.state]
  · intro i
    fin_cases i <;>
      simp [middle,scalarStacks,rawAlphabetEncoded,ScalarSetupProgram.outputState,
        ScalarSetupProgram.state,ScalarSetupProgram.tokenAlphabet_eq,
        CoefficientSearchProgram.inputState,CoefficientSearchProgram.generationInput,
        CoefficientSearchProgram.wide,CoefficientSearchProgram.blank,
        CoefficientCheckerProgram.wide,CoefficientCheckerProgram.lowData,
        MatrixScalarProgram.state,MatrixScalarProgram.scalarStacks,
        CoefficientPascalProgram.valueWords,CoefficientSearchSemantics.scalarTokens,
        CoefficientSearchSemantics.alphabet]
  · intro i hi
    fin_cases i <;>
      simp_all [scalarStacks,Fin.exists_fin_succ,middle,rawInput,
        CoefficientSearchProgram.inputState,CoefficientSearchProgram.generationInput,
        CoefficientSearchProgram.wide,CoefficientSearchProgram.blank,
        CoefficientCheckerProgram.wide,CoefficientCheckerProgram.lowData,
        MatrixScalarProgram.state,MatrixScalarProgram.scalarStacks,
        CoefficientPascalProgram.valueWords]

theorem clear_middle (A R : ℕ) (original : Fin 14 → Bool) (localRegs : Fin 6 → Bool) :
    CoefficientSearchProgram.cleared (middle p A R original localRegs) 20 =
      CoefficientSearchProgram.inputState p A R (lowRegisters original localRegs)
        (original 8) (original 9) (original 10) false false (original 13) := by
  apply state_ext
  · funext i
    fin_cases i <;>
      simp [CoefficientSearchProgram.cleared,readRegs,middle,
        CoefficientSearchProgram.inputState,CoefficientSearchProgram.generationInput,
        CoefficientSearchProgram.wide,CoefficientSearchProgram.blank,
        CoefficientCheckerProgram.wide,CoefficientCheckerProgram.lowData,
        MatrixScalarProgram.state]
  · funext i
    fin_cases i <;>
      simp [CoefficientSearchProgram.cleared,middle,
        CoefficientSearchProgram.inputState,CoefficientSearchProgram.generationInput,
        CoefficientSearchProgram.wide,CoefficientSearchProgram.blank,
        CoefficientCheckerProgram.wide,CoefficientCheckerProgram.lowData,
        MatrixScalarProgram.state,MatrixScalarProgram.scalarStacks,
        CoefficientPascalProgram.valueWords]

/-- Actual setup execution, including the physical raw-alphabet clear. -/
theorem setup_eval (A R : ℕ) (regs : Fin 14 → Bool) :
    ∃ n ≤ ScalarSetupProgram.budget p + 2 * (rawAlphabetEncoded p).length + 3,
      ∃ low : Fin 8 → Bool,
        Eval setup n (rawInput p A R regs)
          (CoefficientSearchProgram.inputState p A R low
            (regs 8) (regs 9) (regs 10) false false (regs 13)) := by
  obtain ⟨localRegs,hr⟩ := ScalarSetupProgram.program_run p (regs ∘ scalarRegisters)
  obtain ⟨n,hn,he⟩ := lifted_call ScalarSetupProgram.program scalarRegisters scalarStacks
    scalarRegisters_injective scalarStacks_injective (rawInput p A R regs)
    (ScalarSetupProgram.outputState p localRegs) (ScalarSetupProgram.budget p)
    (by simpa only [restrict_rawInput] using hr)
  rw [embed_output] at he
  have hc := CoefficientSearchProgram.clear_eval (middle p A R regs localRegs) 20
  have hraw : (middle p A R regs localRegs).stacks 20 = rawAlphabetEncoded p := by
    simp [middle]
  rw [hraw,clear_middle] at hc
  exact ⟨n + (2 * (rawAlphabetEncoded p).length + 3),by omega,
    lowRegisters regs localRegs,he.seq hc⟩

theorem rawAlphabetEncoded_length :
    (rawAlphabetEncoded p).length = 2 * (p * width p) + 2 * p + 1 := by
  rw [rawAlphabetEncoded,ProgramEncoding.encodeRecords_length]
  simp only [ScalarSetupProgram.rawAlphabet,
    List.map_map,Function.comp_def,word_length,List.map_const',
    List.length_map,QuarticSearch.length_elements,List.sum_replicate_nat]

theorem budget_eq : budget p = 105 * p * width p + 108 * p + 74 * width p + 99 := by
  rw [budget,ScalarSetupProgram.budget_eq,rawAlphabetEncoded_length]
  ring

theorem budget_le : budget p ≤ 200 * (p + 1) * (width p + 1) := by
  rw [budget_eq]
  nlinarith

end SubexponentialSAT.Subexp.CoefficientSearchSetup

end OAI.Algorithms
