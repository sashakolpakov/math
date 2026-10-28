import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramParameters
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeParametersProgramBudget
import OAI.Algorithms.SubexponentialSAT.BitProgramSelectedSpace

/-! Actual sparse-code metadata production, with paid polynomial time and every-prefix word bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram

/-- This is precisely the paid outer metadata-stage budget: input copies,
arithmetic, seven unary outputs, output copies and complete worker cleanup. -/
def parameterTime (m B W ml Bl : ℕ) : ℕ :=
  10000 * (W + CodeParametersProgram.fullBudget m B ml Bl + 2)

/-- Actual metadata production preserves all saved high words outside its
fifteen output ports. In particular 768,780,781,783 and817 are preserved. -/
theorem parameters_trace_space (a : Data) {m B W : ℕ} (hm : 0 < m) (hB : 0 < B)
    (he : WorkerEmpty a) (hmv : BinaryArithmetic.toNat (a.stacks 782) = m)
    (hBv : BinaryArithmetic.toNat (a.stacks 786) = B)
    (hW : ∀ i, (a.stacks i).length ≤ W) :
    ∃ steps b, steps ≤ parameterTime m B W (a.stacks 782).length (a.stacks 786).length ∧
      Eval parameters steps a b ∧ WorkerEmpty b ∧ (∀ i, b.regs i = false) ∧
      Metadata m B b ∧
      (b.stacks 800).length ≤ (a.stacks 782).length + (a.stacks 786).length + 11 ∧
      (b.stacks 801).length ≤ 4 * (a.stacks 782).length + 2 * (a.stacks 786).length + 30 ∧
      (∀ i : Fin 896, 768 ≤ i.val → (i.val < 800 ∨ 814 < i.val) →
        b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤
        W + parameterTime m B W (a.stacks 782).length (a.stacks 786).length) ∧
      Trace (compiled parameters 784 788) (steps + 1)
        (a.withPC (some (compiled parameters 784 788).entry)) (b.withPC none) ∧
      ∀ k c, k ≤ steps + 1 → Trace (compiled parameters 784 788) k
        (a.withPC (some (compiled parameters 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤
          W + parameterTime m B W (a.stacks 782).length (a.stacks 786).length + 1 := by
  obtain ⟨steps, ht, b, hrun, hempty, hregs, hmeta, hq, hD, hf⟩ :=
    parameters_eval a hm hB he hmv hBv hW
  change steps ≤ parameterTime m B W (a.stacks 782).length (a.stacks 786).length at ht
  refine ⟨steps, b, ht, hrun, hempty, hregs, hmeta, hq, hD, hf, ?_,
    compiled_halt_trace hrun 784 788, ?_⟩
  · exact SubexpSetupBoundSpec.wordBound_mono
      (SubexpSetupBoundSpec.eval_wordBound hW hrun) (Nat.add_le_add_left ht W)
  · intro k c hk hc i
    have hg : (c.stacks i).length ≤ (a.stacks i).length + k := by
      simpa [selectedStackBits] using trace_selectedStackBits _ {i} hc
    have hi := hW i
    omega

/-- One fixed ordinary polynomial bounds the metadata stage and every
temporary word. Its coefficients and degree precede all input values;
the numerical occurrence bound is not substituted for its word length. -/
theorem parameterTime_polynomial :
    ∃ C d : ℕ, ∀ m B W ml Bl, 0 < m → 0 < B → ml ≤ W → Bl ≤ W →
      W + parameterTime m B W ml Bl + 1 ≤ C * (m + W + 16) ^ d := by
  obtain ⟨C, e, hC⟩ := CodeParametersProgram.runtime_ordinary
  refine ⟨10000 * (C * 2 ^ e + 1) + 1, e + 1, ?_⟩
  intro m B W ml Bl hm hB hml hBl
  let X := m + W + 16
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hinput : CodeParametersProgram.setupInput m ml Bl ≤ 2 * X := by
    dsimp [CodeParametersProgram.setupInput, X]
    omega
  have hbudget : CodeParametersProgram.fullBudget m B ml Bl + 1 ≤
      (C * 2 ^ e) * X ^ e := by
    calc
      _ ≤ C * (CodeParametersProgram.setupInput m ml Bl) ^ e := hC m B ml Bl hm hB
      _ ≤ C * (2 * X) ^ e := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hinput e)
      _ = _ := by rw [mul_pow]; ring
  have hp : X ^ e ≤ X ^ (e + 1) := Nat.pow_le_pow_right hX (by omega)
  have hlinear : X ≤ X ^ (e + 1) := by
    simpa using Nat.pow_le_pow_right hX (by omega : 1 ≤ e + 1)
  have hW : W + 1 ≤ X ^ (e + 1) := by
    apply (show W + 1 ≤ X by dsimp [X]; omega).trans hlinear
  have hb := hbudget.trans (Nat.mul_le_mul_left (C * 2 ^ e) hp)
  unfold parameterTime
  change W + 10000 * (W + CodeParametersProgram.fullBudget m B ml Bl + 2) + 1 ≤
    (10000 * (C * 2 ^ e + 1) + 1) * X ^ (e + 1)
  nlinarith only [hb, hW]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup
