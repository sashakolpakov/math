import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowInputSetup
import OAI.Algorithms.SubexponentialSAT.Subexp.CorrectionVectorExecution
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputTypes

namespace OAI.Algorithms

/-! Typed joins for the actual row-input setup.  The setup output is exactly
the correction-vector input; its first 29 stacks are exactly the type reader's
input.  These identities do not impose any initial Boolean-register values. -/

namespace SubexponentialSAT.Subexp.UniversalRowInputTypes

open BitProgram StructuredCalls MulticolorTypes
open UniversalRowWorkspace (port)

abbrev Data := UniversalRowInputSetup.Data
abbrev Bits := List Bool

private theorem fixedBits_zero (b : ℕ) :
    SubexpLiftRing.fixedBits b 0 = List.replicate b false := by
  induction b with
  | zero => rfl
  | succ b ih => simp [SubexpLiftRing.fixedBits, List.replicate_succ, ih]

theorem word_zero (p : ℕ) [Fact p.Prime] :
    MatrixWordEncoding.word p 0 = List.replicate (MatrixWordEncoding.width p) false := by
  simp [MatrixWordEncoding.word, fixedBits_zero]

variable {r Q Δ : ℕ}

theorem inputStacks_eq_vector (a : Data) (p : ℕ) [Fact p.Prime]
    (i : Fin Δ) (u y : UniversalType r Q Δ) (xs : List (ZMod p))
    (constant shape : Bits) (regs : Fin 10 → Bool)
    (hQ : a.stacks 253 = List.replicate Q true)
    (hr : a.stacks 252 = List.replicate r true)
    (hu : a.stacks 272 = CollisionProgram.encodeType u)
    (hy : a.stacks 275 = CollisionProgram.encodeType y)
    (hi : a.stacks 284 = List.replicate (i.val + 1) true)
    (hm : a.stacks 128 = MatrixWordEncoding.modulus p)
    (hc : a.stacks 254 = MatrixProgramSupport.words (xs.map (MatrixWordEncoding.word p)))
    (hconstant : a.stacks 133 = constant) (hshape : a.stacks 131 = shape) :
    UniversalRowInputSetup.inputStacks a Q r xs.length (MatrixWordEncoding.width p) =
      (CorrectionVectorProgram.input p i u y xs constant shape regs).stacks := by
  funext j
  rw [UniversalRowInputSetup.inputStacks_eq a Q r xs.length
    (MatrixWordEncoding.width p) hQ hr j]
  fin_cases j <;>
    simp +decide [CorrectionVectorProgram.input, CorrectionVectorProgram.state,
      MatrixEntryProgram.typedInput, MatrixEntryProgram.input,
      CoefficientPascalProgram.valueWords, hu, hy, hi, hm, hc, hconstant, hshape, word_zero]

theorem inputStacks_first29 (a : Data) (R b : ℕ)
    (i : Fin Δ) (u y : UniversalType r Q Δ) (regs : Fin 8 → Bool)
    (hQ : a.stacks 253 = List.replicate Q true)
    (hr : a.stacks 252 = List.replicate r true)
    (hu : a.stacks 272 = CollisionProgram.encodeType u)
    (hy : a.stacks 275 = CollisionProgram.encodeType y)
    (hi : a.stacks 284 = List.replicate (i.val + 1) true) :
    (fun j : Fin 29 => UniversalRowInputSetup.inputStacks a Q r R b (Fin.castAdd 20 j)) =
      (MatrixInputTypes.input i u y regs).stacks := by
  funext j
  rw [UniversalRowInputSetup.inputStacks_eq a Q r R b hQ hr (Fin.castAdd 20 j)]
  fin_cases j <;>
    simp +decide [MatrixInputTypes.input, MatrixInputProgram.inputState, hu, hy, hi]

/-- The physical setup directly produces both typed views.  The master
relations are byte encodings of scalar inputs, types and the supplied row;
no computed matrix entry or correction coefficient is a premise. -/
theorem command_eval_typed (a : Data) (p : ℕ) [Fact p.Prime]
    (i : Fin Δ) (u y : UniversalType r Q Δ) (xs : List (ZMod p))
    (constant shape : Bits)
    (hempty : ∀ j, a.stacks (port j) = [])
    (hQ : a.stacks 253 = List.replicate Q true)
    (hr : a.stacks 252 = List.replicate r true)
    (hR : a.stacks 243 = List.replicate (xs.length + 1) true)
    (hwidth : (a.stacks 129).length = MatrixWordEncoding.width p)
    (hzero : a.stacks 131 = List.replicate (4 * MatrixWordEncoding.width p) false)
    (hu : a.stacks 272 = CollisionProgram.encodeType u)
    (hy : a.stacks 275 = CollisionProgram.encodeType y)
    (hi : a.stacks 284 = List.replicate (i.val + 1) true)
    (hm : a.stacks 128 = MatrixWordEncoding.modulus p)
    (hc : a.stacks 254 = MatrixProgramSupport.words (xs.map (MatrixWordEncoding.word p)))
    (hconstant : a.stacks 133 = constant) (hshape : a.stacks 131 = shape) :
    ∃ out : Data,
      Eval UniversalRowInputSetup.command
        (UniversalRowInputSetup.budget a Q r (MatrixWordEncoding.width p)) a out ∧
      (fun j => out.stacks (port j)) =
        (CorrectionVectorProgram.input p i u y xs constant shape
          (fun j => out.regs (Fin.castAdd 6 j))).stacks ∧
      (fun j : Fin 29 => out.stacks (port (Fin.castAdd 20 j))) =
        (MatrixInputTypes.input i u y (fun j => out.regs (Fin.castAdd 8 j))).stacks ∧
      (∀ k, (¬ ∃ j, port j = k) → out.stacks k = a.stacks k) := by
  obtain ⟨out, he, hn, hf⟩ := UniversalRowInputSetup.command_eval a Q r xs.length
    (MatrixWordEncoding.width p) hempty hQ hr hR hwidth hzero
  refine ⟨out, he, ?_, ?_, hf⟩
  · exact (funext hn).trans (inputStacks_eq_vector a p i u y xs constant shape
      (fun j => out.regs (Fin.castAdd 6 j)) hQ hr hu hy hi hm hc hconstant hshape)
  · exact (funext fun j : Fin 29 => hn (Fin.castAdd 20 j)).trans
      (inputStacks_first29 a xs.length (MatrixWordEncoding.width p) i u y
        (fun j => out.regs (Fin.castAdd 8 j)) hQ hr hu hy hi)

end SubexponentialSAT.Subexp.UniversalRowInputTypes

end OAI.Algorithms
