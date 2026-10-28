import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram
import OAI.Algorithms.SubexponentialSAT.ExecQuantitativeSparsify

namespace OAI.Algorithms

/-!+# Canonical-input correctness of the encoded normalizer

The program consumes the body left by the separate header parser. The output
is exactly the typed sparsifier's ordered normalized input. The declared
variable universe is retained, so unused coordinates require no renaming.
-/

namespace SubexponentialSAT.SubexpNormalizationCorrectness

open BitProgram
open SubexpNormalizationProgram (Data Ready formulaCode program)

def normalizedFormula {n : ℕ} (F : SAT.CNF (Fin n)) : ExecSparsifyWorklist.Formula n :=
  ExecSparsifyWorklist.normalizedInput (ExecQuantitativeSparsify.formulaList F)

def normalizedBody {n : ℕ} (F : SAT.CNF (Fin n)) : List Bool :=
  ExecQuantitativeSparsify.encodeRawFormula (normalizedFormula F)

theorem normalized_set {n : ℕ} (F : SAT.CNF (Fin n)) :
    ExecCNF.formulaSet (normalizedFormula F) = SAT.normalize F := by
  simp only [normalizedFormula, ExecSparsifyWorklist.normalizedInput_set,
    ExecQuantitativeSparsify.formulaList_set]

theorem normalized_eval {n : ℕ} (F : SAT.CNF (Fin n)) (a : SAT.Assignment (Fin n)) :
    SAT.CNF.eval a (ExecCNF.formulaSet (normalizedFormula F)) = SAT.CNF.eval a F := by
  rw [normalized_set, SAT.eval_normalize]

theorem normalized_satisfiable {n : ℕ} (F : SAT.CNF (Fin n)) :
    SAT.Satisfiable (ExecCNF.formulaSet (normalizedFormula F)) ↔ SAT.Satisfiable F := by
  rw [normalized_set, SAT.satisfiable_normalize]

theorem canonical_body_eq {n : ℕ} (F : SAT.CNF (Fin n)) :
    formulaCode ((ExecQuantitativeSparsify.formulaList F).map (List.map Encoding.literalCode)) =
      Encoding.encodeCNFBody F :=
  ExecQuantitativeSparsify.encode_formulaList F

theorem normalizedBody_length_le {n : ℕ} (F : SAT.CNF (Fin n)) :
    (normalizedBody F).length ≤ (Encoding.encodeCNFBody F).length := by
  have h := SubexpNormalizationProgram.normalize_length_le
    ((ExecQuantitativeSparsify.formulaList F).map (List.map Encoding.literalCode))
  rw [← ExecCNFCodeTransport.normalizedInput_literalCode, canonical_body_eq] at h
  exact h

/-- The output is the exact ordered list that initializes the typed worklist. -/
theorem canonical_body_runsIn {n : ℕ} (F : SAT.CNF (Fin n)) (d : Data)
    (hsource : d.stacks 13 = Encoding.encodeCNFBody F) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 13 = normalizedBody F ∧
      RunsIn program (3300 * ((Encoding.encodeCNFBody F).length + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  have hs : d.stacks 13 =
      formulaCode ((ExecQuantitativeSparsify.formulaList F).map (List.map Encoding.literalCode)) := by
    simpa only [canonical_body_eq] using hsource
  obtain ⟨e, he, hout, hrun⟩ := SubexpNormalizationProgram.typed_program_runsIn
    (ExecQuantitativeSparsify.formulaList F) d hs hready
  rw [canonical_body_eq] at hrun
  exact ⟨e, he, hout, hrun⟩

theorem canonical_raw_body_runsIn {n : ℕ} (F : SAT.CNF (Fin n)) :
    ∃ e : Data, Ready e ∧ e.stacks 13 = normalizedBody F ∧
      RunsIn program (3300 * ((Encoding.encodeCNFBody F).length + 1) ^ 2)
        (initial program (Encoding.encodeCNFBody F)) (e.withPC none) := by
  let d := SubexpNormalizationProgram.inputData (Encoding.encodeCNFBody F)
  obtain ⟨e, he, hout, hrun⟩ := canonical_body_runsIn F d
    (by simp [d, SubexpNormalizationProgram.inputData])
    (SubexpNormalizationProgram.inputData_ready _)
  exact ⟨e, he, hout, hrun⟩

/-- The bound may use the complete input length although the header is parsed
by a separate program. This theorem does not charge that separate parsing. -/
theorem canonical_body_inputLength_runsIn {n : ℕ} (F : SAT.CNF (Fin n)) (d : Data)
    (hsource : d.stacks 13 = Encoding.encodeCNFBody F) (hready : Ready d) :
    ∃ e : Data, Ready e ∧ e.stacks 13 = normalizedBody F ∧
      RunsIn program (3300 * (Encoding.formulaBitLength F + 1) ^ 2)
        (d.withPC (some program.entry)) (e.withPC none) := by
  obtain ⟨e, he, hout, hrun⟩ := canonical_body_runsIn F d hsource hready
  have hlen : (Encoding.encodeCNFBody F).length + 1 ≤ Encoding.formulaBitLength F + 1 := by
    rw [Encoding.formulaBitLength_eq]
    omega
  exact ⟨e, he, hout, hrun.mono (Nat.mul_le_mul_left 3300 (Nat.pow_le_pow_left hlen 2))⟩

theorem canonical_raw_body_primitive {n : ℕ} (F : SAT.CNF (Fin n)) :
    ∃ e : Data, Ready e ∧ e.stacks 13 = normalizedBody F ∧
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * (3300 * ((Encoding.encodeCNFBody F).length + 1) ^ 2))
        ((primitive program).init (Encoding.encodeCNFBody F))
        (primitiveCfg program (e.withPC none)) := by
  obtain ⟨e, he, hout, hrun⟩ := canonical_raw_body_runsIn F
  exact ⟨e, he, hout, by simpa only [primitive_initial] using primitive_execution program hrun⟩

end SubexponentialSAT.SubexpNormalizationCorrectness

end OAI.Algorithms
