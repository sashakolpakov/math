import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CorrectionScalarNegation
import OAI.Algorithms.SubexponentialSAT.Subexp.CorrectionScalarEmbedding

namespace OAI.Algorithms

/-! The actual per-entry arithmetic/output step of the correction-vector loop. -/

namespace SubexponentialSAT.Subexp.CorrectionScalarProgram

open BitProgram StructuredCalls BinaryArithmetic ModularArithmetic
open CorrectionScalarNegation (Data Word)

abbrev command : Cmd 10 49 :=
  .seq CorrectionScalarNegation.command CorrectionScalarEmbedding.command

theorem command_eval (input modulus constant shape : Word) (width : ℕ) (a : Data)
    (hi : a.stacks 0 = input) (hm : a.stacks 29 = modulus) (hc : a.stacks 46 = constant)
    (hs : a.stacks 47 = shape)
    (hwork : ∀ j : Fin 49, j ∈ [1, 2, 3, 4, 6, 7] → a.stacks j = [])
    (hiw : input.length = width) (hcw : constant.length = width)
    (hsw : shape.length = 4 * width) (hmw : modulus.length ≤ width + 1)
    (hmpos : 0 < BinaryArithmetic.toNat modulus) (hcapacity : BinaryArithmetic.toNat modulus ≤ 2 ^ width)
    (hconstant : BinaryArithmetic.toNat constant = BinaryArithmetic.toNat modulus - 1) :
    ∃ n ≤ 6010 * (width + 1) ^ 2 + 44 * width + 8,
      ∃ scalar : Word, ∃ b : Data,
        Eval command n a b ∧ scalar.length = width ∧
        (BinaryArithmetic.toNat scalar : ZMod (BinaryArithmetic.toNat modulus)) = -(BinaryArithmetic.toNat input : ZMod (BinaryArithmetic.toNat modulus)) ∧
        b.stacks = Function.update (Function.update a.stacks 0 []) 43
          ((scalar ++ List.replicate (3 * width) false).reverse ++ a.stacks 43) := by
  obtain ⟨nn, hnn, scalar, mid, hn, hlen, hvalue, hmid⟩ :=
    CorrectionScalarNegation.command_eval input modulus constant width a hi hm hc hwork
      hiw hcw hmw hmpos hcapacity hconstant
  obtain ⟨b, he, hb⟩ := CorrectionScalarEmbedding.command_eval scalar shape mid
    (by simp [hmid]) (by simpa [hmid] using hs)
    (by simpa [hmid] using hwork 1 (by simp))
    (by simpa [hmid] using hwork 2 (by simp)) (by omega)
  refine ⟨nn + (11 * shape.length + 8), ?_, scalar, b, hn.seq he, hlen, hvalue, ?_⟩
  · rw [hsw]
    omega
  · rw [hb, CorrectionScalarEmbedding.quartet_shape shape scalar width hsw hlen, hmid]
    simp

end SubexponentialSAT.Subexp.CorrectionScalarProgram

end OAI.Algorithms
