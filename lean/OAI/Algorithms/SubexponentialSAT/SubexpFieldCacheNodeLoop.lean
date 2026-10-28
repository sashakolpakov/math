import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFieldCacheMachine

namespace OAI.Algorithms

/-! Actual all-node scan and exact packed-array order. -/

namespace SubexponentialSAT.SubexpFieldCacheNodeLoop

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open SubexpCRTCofactorControl SubexpFieldCacheControl SubexpFieldCacheLoop
open SubexpQuarticFlatMul (flat)
open SubexpFieldCacheMachine (negate power nodeIterationBudget)

def ready (base : Words) (stream accumulator : List Bool) : Words :=
  {base with
    stream := stream, accumulator := accumulator
    node := [], negative := [], power := [], left := [], right := [], result := []}

def negativeBytes (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)
    (minusOne : Word (baseWidth p μ)) (xs : List (Quad (Word (baseWidth p μ)))) : List Bool :=
  xs.flatMap fun a => flat (SubexpQuarticNegMachine.negateWords p μ M minusOne a)

noncomputable def PowerValue (p μ : ℕ) (c : Fin 4 → ZMod (p^μ)) (exponent : List Bool)
    (a b : Quad (Word (baseWidth p μ))) : Prop :=
  quotientDenote c (b.map (wordValue p μ)) =
    quotientDenote c (a.map (wordValue p μ)) ^ BinaryArithmetic.toNat exponent

/-- The loop itself chooses no semantic output words. Each output is obtained
from the actual power execution, then emitted into the packed accumulator. -/
theorem loop_value (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (c : Fin 4 → ZMod (p^μ))
    (t unit : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (base : Words) (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hone : base.unit = flat unit) (hmone : base.minusOne = minusOne.val)
    (hw : base.width.length = baseWidth p μ)
    (hblock : base.blockWidth.length = 4 * baseWidth p μ) (hB : 0 < baseWidth p μ)
    (xs : List (Quad (Word (baseWidth p μ)))) (regs : Fin 8 → Bool)
    (frame : Fin 110 → List Bool) (acc : List Bool) :
    ∃ n rf ys, n ≤ xs.length * (nodeIterationBudget (baseWidth p μ) base.exponent + 2) + 1 ∧
      List.Forall₂ (PowerValue p μ c base.exponent) xs ys ∧
      Eval (.while 1 (.seq (nodeIteration negate power) (peek 99))) n
        (state (readRegs regs 0 1 (xs.flatMap flat).head?) frame (ready base (xs.flatMap flat) acc))
        (state rf
          (Function.update frame 100 ((negativeBytes p μ M minusOne xs).reverse ++ frame 100))
          (ready base [] ((ys.flatMap flat).reverse ++ acc))) := by
  induction xs generalizing regs frame acc with
  | nil =>
      refine ⟨1, readRegs regs 0 1 none, [], by simp, .nil, ?_⟩
      simp only [List.flatMap_nil, negativeBytes, List.reverse_nil, List.nil_append,
        Function.update_eq_self]
      exact Eval.while_false (by simp [state, readRegs])
  | cons a xs ih =>
      let r0 := readRegs regs 0 1 ((a :: xs).flatMap flat).head?
      let w0 := ready base ((a :: xs).flatMap flat) acc
      obtain ⟨n, r1, b, hn, he, hv⟩ := SubexpFieldCacheMachine.nodeIteration_value
        p μ M c t unit a minusOne ht hu r0 frame w0 (xs.flatMap flat)
        hm hr hone hmone rfl hw hblock rfl rfl rfl rfl rfl rfl
      let f1 := Function.update frame 100
        ((flat (SubexpQuarticNegMachine.negateWords p μ M minusOne a)).reverse ++ frame 100)
      let acc1 := (flat b).reverse ++ acc
      have he' : Eval (nodeIteration negate power) n (state r0 frame w0)
          (state r1 f1 (ready base (xs.flatMap flat) acc1)) := he
      have hp := SubexpCRTCofactorLoop.peekNodes_eval r1 f1 (ready base (xs.flatMap flat) acc1)
      obtain ⟨m, rf, ys, hm', hys, hi⟩ := ih r1 f1 acc1
      have hne : flat a ≠ [] := by
        intro hz
        have hh := congrArg List.length hz
        simp only [SubexpQuarticFlatMul.flat_length, List.length_nil] at hh
        omega
      have hg : (state r0 frame w0).regs 1 = true := by
        cases ha : flat a with
        | nil => exact False.elim (hne ha)
        | cons bit bits => simp [r0, state, readRegs, ha]
      have hh := Eval.while_true hg (he'.seq hp) hi
      refine ⟨n + 1 + m + 1, rf, b :: ys, ?_, .cons hv hys, ?_⟩
      · change n ≤ nodeIterationBudget (baseWidth p μ) base.exponent at hn
        simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · simpa only [SubexpCRTCofactorControl.peekNodes, peek, ready, r0, w0,
          negativeBytes, List.flatMap_cons, List.reverse_append, List.append_assoc,
          Function.update_same, Function.update_idem, f1, acc1] using hh

theorem scan_value (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (c : Fin 4 → ZMod (p^μ))
    (t unit : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (base : Words) (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hone : base.unit = flat unit) (hmone : base.minusOne = minusOne.val)
    (hw : base.width.length = baseWidth p μ)
    (hblock : base.blockWidth.length = 4 * baseWidth p μ) (hB : 0 < baseWidth p μ)
    (xs : List (Quad (Word (baseWidth p μ)))) (regs : Fin 8 → Bool)
    (frame : Fin 110 → List Bool) (acc : List Bool) :
    ∃ n rf ys, n ≤ xs.length * (nodeIterationBudget (baseWidth p μ) base.exponent + 2) + 2 ∧
      List.Forall₂ (PowerValue p μ c base.exponent) xs ys ∧
      Eval (.seq (peek 99) (.while 1 (.seq (nodeIteration negate power) (peek 99)))) n
        (state regs frame (ready base (xs.flatMap flat) acc))
        (state rf
          (Function.update frame 100 ((negativeBytes p μ M minusOne xs).reverse ++ frame 100))
          (ready base [] ((ys.flatMap flat).reverse ++ acc))) := by
  obtain ⟨n, rf, ys, hn, hv, he⟩ := loop_value p μ M c t unit minusOne ht hu base
    hm hr hone hmone hw hblock hB xs regs frame acc
  have hp := SubexpCRTCofactorLoop.peekNodes_eval regs frame (ready base (xs.flatMap flat) acc)
  exact ⟨1 + n, rf, ys, by omega, hv, hp.seq he⟩

theorem flatMap_length {B : ℕ} (xs : List (Quad (Word B))) :
    (xs.flatMap flat).length = 4 * B * xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp [ih, SubexpQuarticFlatMul.flat_length, Nat.mul_add, Nat.add_comm]

theorem negativeBytes_length (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (minusOne : Word (baseWidth p μ))
    (xs : List (Quad (Word (baseWidth p μ)))) :
    (negativeBytes p μ M minusOne xs).length = 4 * baseWidth p μ * xs.length := by
  induction xs with
  | nil => simp [negativeBytes]
  | cons a xs ih =>
      simp only [negativeBytes, List.flatMap_cons, List.length_append,
        SubexpQuarticFlatMul.flat_length, List.length_cons, Nat.mul_add, Nat.mul_one] at ih ⊢
      omega

def passBudget (B : ℕ) (exponent : List Bool) (count : ℕ) : ℕ :=
  count * (nodeIterationBudget B exponent + 100 * B + 2) + 21

/-- The complete node pass preserves the original packed node array at97
and writes correctly ordered inverse98 and negative100 arrays. -/
theorem pass_value (p μ : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p μ) (c : Fin 4 → ZMod (p^μ))
    (t unit : Quad (Word (baseWidth p μ))) (minusOne : Word (baseWidth p μ))
    (ht : t.map (wordValue p μ) = reductionData c)
    (hu : quotientDenote c (unit.map (wordValue p μ)) = 1)
    (base : Words) (hm : base.modulus = M.bits) (hr : base.reduction = flat t)
    (hone : base.unit = flat unit) (hmone : base.minusOne = minusOne.val)
    (hw : base.width.length = baseWidth p μ)
    (hblock : base.blockWidth.length = 4 * baseWidth p μ) (hB : 0 < baseWidth p μ)
    (xs : List (Quad (Word (baseWidth p μ)))) (regs : Fin 8 → Bool)
    (frame : Fin 110 → List Bool) (htable : frame 97 = xs.flatMap flat) (hzero : frame 100 = []) :
    ∃ n rf ys, n ≤ passBudget (baseWidth p μ) base.exponent xs.length ∧
      List.Forall₂ (PowerValue p μ c base.exponent) xs ys ∧
      Eval (nodePass negate power) n (state regs frame (ready base [] []))
        (state rf (Function.update frame 100 (negativeBytes p μ M minusOne xs))
          (ready base [] (ys.flatMap flat))) := by
  let r1 := readRegs regs 0 1 none
  have hcopy := copy_extra_stream_eval regs frame (ready base [] []) 97
    (by left; rfl) rfl
  have hcopy' : Eval (SubexpFieldCacheControl.copy 97 99)
      (7 * (xs.flatMap flat).length + 5) (state regs frame (ready base [] []))
      (state r1 frame (ready base (xs.flatMap flat) [])) := by
    simpa only [htable, r1, ready] using hcopy
  obtain ⟨ns, rs, ys, hns, hv, hs⟩ := scan_value p μ M c t unit minusOne ht hu base
    hm hr hone hmone hw hblock hB xs r1 frame []
  let f1 := Function.update frame 100 (negativeBytes p μ M minusOne xs).reverse
  have hs' : Eval (.seq (peek 99) (.while 1 (.seq (nodeIteration negate power) (peek 99)))) ns
      (state r1 frame (ready base (xs.flatMap flat) []))
      (state rs f1 (ready base [] (ys.flatMap flat).reverse)) := by
    simpa only [hzero, List.append_nil, f1] using hs
  have hri := reverse_inverse_eval rs f1 (ready base [] (ys.flatMap flat).reverse)
  have hrn := reverse_extra_eval (readRegs rs 0 1 none) f1 (ready base [] (ys.flatMap flat))
    100 (by right; left; rfl)
  have hrn' : Eval (SubexpFieldCacheControl.reverse 100)
      (9 * (negativeBytes p μ M minusOne xs).length + 7)
      (state (readRegs rs 0 1 none) f1 (ready base [] (ys.flatMap flat)))
      (state (readRegs rs 0 1 none)
        (Function.update frame 100 (negativeBytes p μ M minusOne xs))
        (ready base [] (ys.flatMap flat))) := by
    simpa only [f1, Function.update_same, Function.update_idem,
      List.reverse_reverse, List.length_reverse, StackRoutines.readRegs_reset] using hrn
  have hri' : Eval (SubexpFieldCacheControl.reverse 98)
      (9 * (ys.flatMap flat).length + 7)
      (state rs f1 (ready base [] (ys.flatMap flat).reverse))
      (state (readRegs rs 0 1 none) f1 (ready base [] (ys.flatMap flat))) := by
    simpa only [ready, List.reverse_reverse, List.length_reverse] using hri
  have he := hcopy'.seq (SubexpCRTCofactorLoop.seq_assoc (hs'.seq (hri'.seq hrn')))
  have hlen : ys.length = xs.length := hv.length_eq.symm
  refine ⟨_, readRegs rs 0 1 none, ys, ?_, hv, he⟩
  rw [flatMap_length, flatMap_length, negativeBytes_length, hlen]
  unfold passBudget
  nlinarith only [hns]

end SubexponentialSAT.SubexpFieldCacheNodeLoop

end OAI.Algorithms
