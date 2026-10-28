import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CandidatePrepareProgram
import OAI.Algorithms.SubexponentialSAT.ExecSelectedFamilySize

namespace OAI.Algorithms

/-! Input-bit bounds for the concrete candidate preparation pipeline. -/

namespace SubexponentialSAT.CandidatePrepareProgram

def inputBits (F : Formula) (mask limit : List Bool) (words : List (List Bool)) : ℕ :=
  (formulaCode F).length + (tupleCode (mask :: words)).length + limit.length

/-- The gathered family may repeat clauses for an arbitrary input tuple. Its
encoded size is still polynomial in the original formula and tuple lengths. -/
theorem selected_length_le (F : Formula) (words : List (List Bool)) :
    (formulaCode (selected F words)).length ≤
      2 * ((formulaCode F).length + 1) * ((tupleCode words).length + 1) :=
  ExecSelectedFamilySize.clause_family_output_length_le F words

/-- All parsing, comparison, repeated lookup, core selection, and cleanup
costs fit one quadratic in the actual supplied bits. -/
theorem bound_le_square (F : Formula) (mask limit : List Bool)
    (words : List (List Bool)) :
    bound F mask limit words ≤ 600 * (inputBits F mask limit words + 1) ^ 2 := by
  let A := (formulaCode F).length
  let T := (tupleCode (mask :: words)).length
  let I := (tupleCode words).length
  let B := limit.length
  let L := A + T + B + 1
  have hIT : I ≤ T := by
    dsimp [I, T, tupleCode]
    rw [Encoding.length_encodeList_cons]
    omega
  have hMT : mask.length ≤ T := by
    dsimp [T, tupleCode]
    rw [Encoding.length_encodeList_cons]
    simp only [id_eq]
    omega
  have hA : A + 1 ≤ L := by dsimp [L]; omega
  have hI : I + 1 ≤ L := by dsimp [L]; omega
  have hBI : B + I + 1 ≤ L := by dsimp [L]; omega
  have hprod : (A + 1) * (I + 1) ≤ L ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hA hI
  have hguard : (B + I + 1) * (I + 1) ≤ L ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hBI hI
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hsq : L ≤ L ^ 2 := by
    simpa only [Nat.mul_one, pow_two] using Nat.mul_le_mul_left L hL
  have hout := selected_length_le F words
  change (formulaCode (selected F words)).length ≤ 2 * (A + 1) * (I + 1) at hout
  have hsplit := ExecCNFTupleSplit.cost_le_linear mask words
  change ExecCNFTupleSplit.cost mask words ≤ 16 * T + 7 at hsplit
  change ExecCNFTupleSplit.cost mask words + 240 * (B + I + 1) * (I + 1) +
    128 * (A + 1) * (I + 1) +
    (50 * (formulaCode (selected F words)).length + 50) +
    2 * mask.length + 2 * I + 20 ≤ 600 * L ^ 2
  dsimp [L] at *
  nlinarith

theorem program_runsIn_quadratic (F : Formula) (mask limit : List Bool)
    (words : List (List Bool)) (d : Data) (h : Ready F mask limit words d) :
    ∃ e : Data, BitProgram.RunsIn program (600 * (inputBits F mask limit words + 1) ^ 2)
      (d.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks = outputStacks F mask limit words d ∧ e.regs 30 = valid limit words := by
  obtain ⟨e, he, hs, hg⟩ := program_runsIn F mask limit words d h
  exact ⟨e, he.mono (bound_le_square F mask limit words), hs, hg⟩

theorem primitive_quadratic (F : Formula) (mask limit : List Bool)
    (words : List (List Bool)) (d : Data) (h : Ready F mask limit words d) :
    ∃ e : Data, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (600 * (inputBits F mask limit words + 1) ^ 2))
      (BitProgram.primitiveCfg program (d.withPC (some program.entry)))
      (BitProgram.primitiveCfg program (e.withPC none)) ∧
      e.stacks = outputStacks F mask limit words d ∧ e.regs 30 = valid limit words := by
  obtain ⟨e, he, hs, hg⟩ := program_runsIn_quadratic F mask limit words d h
  exact ⟨e, BitProgram.primitive_execution program he, hs, hg⟩

end SubexponentialSAT.CandidatePrepareProgram

end OAI.Algorithms
