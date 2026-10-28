import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CorrectionScalarProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixWordEncoding

namespace OAI.Algorithms

/-! Exact canonical bytes for the arithmetic step of the correction vector. -/

namespace SubexponentialSAT.Subexp.CorrectionScalarCanonical

open BitProgram StructuredCalls BinaryArithmetic ModularArithmetic
open ModularRingPrograms ModularDivisionPrograms MatrixWordEncoding
open CorrectionScalarNegation (Data Word regMap stackMap regMap_injective stackMap_injective)

variable (p : ℕ) [Fact p.Prime]

theorem negation_eval (x : ZMod p) (constant : Word) (a : Data)
    (hi : a.stacks 0 = word p x) (hm : a.stacks 29 = modulus p)
    (hc : a.stacks 46 = constant)
    (hwork : ∀ j : Fin 49, j ∈ [1, 2, 3, 4, 6, 7] → a.stacks j = [])
    (hcw : constant.length = width p) (hcv : BinaryArithmetic.toNat constant = p - 1) :
    ∃ n ≤ 6010 * (width p + 1)^2, ∃ b : Data,
      Eval CorrectionScalarNegation.command n a b ∧
      b.stacks = Function.update a.stacks 0 (word p (-x)) := by
  obtain ⟨rf, bits, ⟨n, hn, ht⟩, hlen, hv⟩ := SubexpNegationProgram.negation_value
    (a.regs ∘ regMap) (word p x) (modulus p) constant (width p)
    (word_length p x) hcw (by simp) (modulus_positive p)
    (by simpa only [modulus_value] using modulus_capacity p)
    (by simpa only [modulus_value] using hcv)
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hcanonical : BinaryArithmetic.toNat bits < p := by
    rw [hv, modulus_value]
    exact Nat.mod_lt _ hp
  have hfield : (BinaryArithmetic.toNat bits : ZMod p) = -x := by
    rw [hv, modulus_value, ZMod.natCast_mod,
      Nat.cast_sub (Nat.mod_lt _ hp).le, ZMod.natCast_self,
      ZMod.natCast_mod, word_field_value, zero_sub]
  have hbits := word_unique p (-x) bits hlen hcanonical hfield
  subst bits
  let first : State 8 9 := ⟨a.regs ∘ regMap,
    SubexpNegationProgram.state (word p x) (modulus p) constant⟩
  let last : State 8 9 := ⟨rf,
    SubexpNegationProgram.state (word p (-x)) (modulus p) constant⟩
  have hin : embedState regMap stackMap a first = a := by
    apply embedState_eq_of_ports _ _ _ _ _ regMap_injective stackMap_injective
    · intros; rfl
    · intros; rfl
    · intro j
      fin_cases j <;>
        simp [first, stackMap, SubexpNegationProgram.state, SubexpNegationProgram.extendEight,
          extendSeven, resting, seven, hi, hm, hc,
          hwork 1 (by simp), hwork 2 (by simp), hwork 3 (by simp),
          hwork 4 (by simp), hwork 6 (by simp), hwork 7 (by simp)]
    · intros; rfl
  let b := embedState regMap stackMap a last
  have he : Eval CorrectionScalarNegation.command n a b := by
    have h := eval_call_lifted SubexpNegationProgram.negationProgram regMap stackMap a
      regMap_injective stackMap_injective (a := first) (b := last) ht
    simpa only [CorrectionScalarNegation.command, b, hin] using h
  refine ⟨n, hn, b, he, ?_⟩
  funext j
  by_cases hj : ∃ k, stackMap k = j
  · obtain ⟨k, rfl⟩ := hj
    rw [show b.stacks (stackMap k) = last.stacks k from
      embedState_stack _ _ _ _ stackMap_injective k]
    fin_cases k <;>
      simp [last, stackMap, SubexpNegationProgram.state, SubexpNegationProgram.extendEight,
        extendSeven, resting, seven, hm, hc,
        hwork 1 (by simp), hwork 2 (by simp), hwork 3 (by simp),
        hwork 4 (by simp), hwork 6 (by simp), hwork 7 (by simp)]
  · rw [show b.stacks j = a.stacks j from embedState_stack_frame _ _ _ _ j hj]
    have h0 : j ≠ 0 := fun h => hj ⟨0, h.symm⟩
    simp [h0]

def quartet (x : ZMod p) : Word := word p x ++ List.replicate (3 * width p) false

omit [Fact (Nat.Prime p)] in
@[simp] theorem quartet_length (x : ZMod p) : (quartet p x).length = 4 * width p := by
  simp [quartet]
  omega

theorem command_eval (x : ZMod p) (constant shape : Word) (a : Data)
    (hi : a.stacks 0 = word p x) (hm : a.stacks 29 = modulus p)
    (hc : a.stacks 46 = constant) (hs : a.stacks 47 = shape)
    (hwork : ∀ j : Fin 49, j ∈ [1, 2, 3, 4, 6, 7] → a.stacks j = [])
    (hcw : constant.length = width p) (hcv : BinaryArithmetic.toNat constant = p - 1)
    (hsw : shape.length = 4 * width p) :
    ∃ n ≤ 6010 * (width p + 1)^2 + 44 * width p + 8, ∃ b : Data,
      Eval CorrectionScalarProgram.command n a b ∧
      b.stacks = Function.update (Function.update a.stacks 0 []) 43
        ((quartet p (-x)).reverse ++ a.stacks 43) := by
  obtain ⟨nn, hnn, mid, hn, hmid⟩ := negation_eval p x constant a hi hm hc hwork hcw hcv
  obtain ⟨b, he, hb⟩ := CorrectionScalarEmbedding.command_eval (word p (-x)) shape mid
    (by simp [hmid]) (by simpa [hmid] using hs)
    (by simpa [hmid] using hwork 1 (by simp))
    (by simpa [hmid] using hwork 2 (by simp)) (by simp [hsw]; omega)
  refine ⟨nn + (11 * shape.length + 8), ?_, b, hn.seq he, ?_⟩
  · rw [hsw]
    omega
  · rw [hb, CorrectionScalarEmbedding.quartet_shape shape (word p (-x)) (width p)
      hsw (word_length p (-x)), hmid]
    simp [quartet]

end SubexponentialSAT.Subexp.CorrectionScalarCanonical

end OAI.Algorithms
