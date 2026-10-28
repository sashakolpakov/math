import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramReuse

namespace OAI.Algorithms

/-! Exact nonnegative component-mass contracts for the actual signed arithmetic
programs. These bounds control both components even when cancellation occurs. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ArithmeticCalls

def pairTotal (positive negative : List Bool) : ℕ := BinaryArithmetic.toNat positive+BinaryArithmetic.toNat negative

private theorem total_scoreCall_eval (ports : Fin 12 → Fin 15)
    (hp : Function.Injective ports) (d : Data)
    (hd : PackingProgram.arithmeticReady (readScore ports d)) :
    ∃ t ≤ 300 * (PackingProgram.arithmeticInputLength (readScore ports d) + 3)^2 + 1,
    ∃ e : Data, Eval (scoreCall ports) t d e ∧
      BinaryArithmetic.toNat (e.stacks (ports 6)) = PackingProgram.weightedScoreValue (readScore ports d) ∧
      (e.stacks (ports 6)).length ≤
        PackingProgram.arithmeticInputLength (readScore ports d) + 3 ∧
      (∀ j, j ≠ ports 4 → j ≠ ports 5 → j ≠ ports 6 → e.stacks j = d.stacks j) := by
  obtain ⟨t, ht, out, he, hv, hl, hf⟩ :=
    PackingProgram.weightedScoreCommand_eval (readScore ports d) hd
  have hs : embedState id ports d (readScore ports d) = d := by
    apply embedState_eq_of_ports id ports d d _ Function.injective_id hp
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i; rfl
    · intro i hi; rfl
  refine ⟨t+1, by omega, embedState id ports d out, ?_, ?_, ?_, ?_⟩
  · have h := eval_call_lifted PackingProgram.weightedScoreProgram id ports d
      Function.injective_id hp (compiled_halt_trace he 0 6)
    simpa only [hs, scoreCall] using h
  · simpa only [embedState_stack id ports d out hp] using hv
  · simpa only [embedState_stack id ports d out hp] using hl
  · intro j h4 h5 h6
    classical
    by_cases hj : ∃ i, ports i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_stack id ports d out hp]
      exact hf i (fun hi => h4 (congrArg ports hi))
        (fun hi => h5 (congrArg ports hi)) (fun hi => h6 (congrArg ports hi))
    · exact embedState_stack_frame id ports d out j hj

theorem multiplyCommand_eval_total (d : Data) (hd : Ready d) :
    ∃ t ≤ 600 * (inputLength d + 3)^2 + 2, ∃ e : Data,
      Eval multiplyCommand t d e ∧
      signedValue (e.stacks 6) (e.stacks 9) =
        signedValue (d.stacks 0) (d.stacks 1) *
          signedValue (d.stacks 2) (d.stacks 3) ∧
      pairTotal (e.stacks 6) (e.stacks 9) =
        pairTotal (d.stacks 0) (d.stacks 1) * pairTotal (d.stacks 2) (d.stacks 3) ∧
      (e.stacks 6).length ≤ inputLength d + 3 ∧
      (e.stacks 9).length ≤ inputLength d + 3 ∧
      (∀ j : Fin 15, j.val < 4 ∨ 10 ≤ j.val → e.stacks j = d.stacks j) := by
  have hp : PackingProgram.arithmeticReady (readScore positivePorts d) := by
    intro j hj
    have hj' : 4 ≤ (positivePorts j).val := by
      fin_cases j <;> norm_num [positivePorts] at *
    exact hd _ hj'
  obtain ⟨tp, htp, middle, he1, hv1, hl1, hf1⟩ :=
    total_scoreCall_eval positivePorts positivePorts_injective d hp
  have hm (j : Fin 15) (hj : j ≠ 4 ∧ j ≠ 5 ∧ j ≠ 6) :
      middle.stacks j = d.stacks j := hf1 j hj.1 hj.2.1 hj.2.2
  have hn : PackingProgram.arithmeticReady (readScore negativePorts middle) := by
    intro j hj
    change middle.stacks (negativePorts j) = []
    have hj' : 4 ≤ (negativePorts j).val := by
      fin_cases j <;> norm_num [negativePorts] at *
    have hn4 : negativePorts j ≠ 4 := by fin_cases j <;> decide
    have hn5 : negativePorts j ≠ 5 := by fin_cases j <;> decide
    have hn6 : negativePorts j ≠ 6 := by fin_cases j <;> decide
    rw [hm _ ⟨hn4, hn5, hn6⟩]
    exact hd _ hj'
  obtain ⟨tn, htn, out, he2, hv2, hl2, hf2⟩ :=
    total_scoreCall_eval negativePorts negativePorts_injective middle hn
  have hlen1 : PackingProgram.arithmeticInputLength (readScore positivePorts d) =
      inputLength d := by
    simp [PackingProgram.arithmeticInputLength, readScore, positivePorts, inputLength]
    omega
  have hlen2 : PackingProgram.arithmeticInputLength (readScore negativePorts middle) =
      inputLength d := by
    simp [PackingProgram.arithmeticInputLength, readScore, negativePorts, inputLength,
      hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide)]
    omega
  have hpout : out.stacks 6 = middle.stacks 6 := hf2 6 (by decide) (by decide) (by decide)
  refine ⟨tp+tn, by rw [hlen1] at htp; rw [hlen2] at htn; omega,
    out, he1.seq he2, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [signedValue, hpout]
    simp [PackingProgram.weightedScoreValue, readScore, positivePorts] at hv1
    simp [PackingProgram.weightedScoreValue, readScore, negativePorts,
      hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide)] at hv2
    rw [hv1, hv2]
    push_cast
    ring
  · simp only [pairTotal, hpout]
    simp [PackingProgram.weightedScoreValue, readScore, positivePorts] at hv1
    simp [PackingProgram.weightedScoreValue, readScore, negativePorts,
      hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide)] at hv2
    rw [hv1,hv2]
    ring
  · change (middle.stacks 6).length ≤ _ at hl1
    rw [hlen1] at hl1
    simpa only [hpout] using hl1
  · change (out.stacks 9).length ≤ _ at hl2
    rwa [hlen2] at hl2
  · intro j hj
    have h4 : j ≠ 4 := by
      intro h
      have hh : j.val = 4 := congrArg Fin.val h
      omega
    have h5 : j ≠ 5 := by
      intro h
      have hh : j.val = 5 := congrArg Fin.val h
      omega
    have h6 : j ≠ 6 := by
      intro h
      have hh : j.val = 6 := congrArg Fin.val h
      omega
    have h7 : j ≠ 7 := by
      intro h
      have hh : j.val = 7 := congrArg Fin.val h
      omega
    have h8 : j ≠ 8 := by
      intro h
      have hh : j.val = 8 := congrArg Fin.val h
      omega
    have h9 : j ≠ 9 := by
      intro h
      have hh : j.val = 9 := congrArg Fin.val h
      omega
    exact (hf2 j h7 h8 h9).trans (hf1 j h4 h5 h6)

theorem addCommand_eval_total (d : Data) (hd : Ready d) :
    ∃ t ≤ 200 * (inputLength d + 1)^2, ∃ e : Data,
      Eval addCommand t d e ∧
      signedValue (e.stacks 6) (e.stacks 9) =
        signedValue (d.stacks 0) (d.stacks 1) + signedValue (d.stacks 2) (d.stacks 3) ∧
      pairTotal (e.stacks 6) (e.stacks 9) =
        pairTotal (d.stacks 0) (d.stacks 1) + pairTotal (d.stacks 2) (d.stacks 3) ∧
      (e.stacks 6).length + (e.stacks 9).length ≤ inputLength d + 2 ∧
      (∀ j : Fin 15, j ≠ 6 → j ≠ 9 → e.stacks j = d.stacks j) := by
  have hp : Valid addPositivePorts d := by
    constructor
    · exact hd 6 (by decide)
    · intro i
      exact hd (addWork i) (by
        change 4 ≤ i.val + 10
        omega)
  obtain ⟨tp, rp, wp, hep, hvp, hlp, htp⟩ := addAt_eval addPositivePorts d hp
  let middle : Data := ⟨rp, Function.update d.stacks 6 wp⟩
  have hn : Valid addNegativePorts middle := by
    constructor
    · simpa [middle, addNegativePorts] using hd 9 (by decide)
    · intro i
      have hi : addWork i ≠ 6 := by fin_cases i <;> decide
      simpa [middle, addNegativePorts, hi] using hd (addWork i) (by
        change 4 ≤ i.val + 10
        omega)
  obtain ⟨tn, rn, wn, hen, hvn, hln, htn⟩ := addAt_eval addNegativePorts middle hn
  let out : Data := ⟨rn, Function.update middle.stacks 9 wn⟩
  have hpbound : (d.stacks addPositivePorts.left).length +
      (d.stacks addPositivePorts.right).length + 1 ≤ inputLength d + 1 := by
    dsimp [addPositivePorts, inputLength]; omega
  have hnbound : (middle.stacks addNegativePorts.left).length +
      (middle.stacks addNegativePorts.right).length + 1 ≤ inputLength d + 1 := by
    simp [middle, addNegativePorts, inputLength]; omega
  have htp' := htp.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hpbound 2))
  have htn' := htn.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hnbound 2))
  refine ⟨tp+tn, by omega, out, hep.seq hen, ?_, ?_, ?_, ?_⟩
  · simp [addPositivePorts] at hvp
    simp [middle, addNegativePorts] at hvn
    simp [out, middle, signedValue, hvp, hvn]
    ring
  · simp [addPositivePorts] at hvp
    simp [middle, addNegativePorts] at hvn
    simp [out,middle,pairTotal,hvp,hvn]
    omega
  · simp [addPositivePorts] at hlp
    simp [middle, addNegativePorts] at hln
    simp [out, middle, inputLength]
    omega
  · intro j h6 h9
    simp [out, middle, h6, h9]

private theorem total_initial_stack_bound (d : Data) (hd : Ready d) (j : Fin 15) :
    (d.stacks j).length ≤ inputLength d := by
  by_cases hj : j.val < 4
  · fin_cases j <;> simp_all [inputLength] <;> omega
  · rw [hd j (by omega)]
    simp

theorem multiplyReuseCommand_eval_total (d : Data) (hd : Ready d) :
    ∃ t ≤ 25000*(inputLength d+3)^2, ∃ regs positive negative,
      Eval multiplyReuseCommand t d (pairState regs positive negative) ∧
      signedValue positive negative =
        signedValue (d.stacks 0) (d.stacks 1) * signedValue (d.stacks 2) (d.stacks 3) ∧
      pairTotal positive negative =
        pairTotal (d.stacks 0) (d.stacks 1) * pairTotal (d.stacks 2) (d.stacks 3) ∧
      positive.length + negative.length ≤ 2*inputLength d+6 := by
  obtain ⟨tm, htm, m, hem, hv, htotal, hp, hn, hf⟩ := multiplyCommand_eval_total d hd
  have hm (j : Fin 15) : (m.stacks j).length ≤ inputLength d+tm := by
    exact (eval_stack_length hem j).trans (Nat.add_le_add_right (total_initial_stack_bound d hd j) tm)
  have hf' (j : Fin 15) (hj : 10 ≤ j.val) : m.stacks j = [] := by
    rw [hf j (Or.inr hj), hd j (by omega)]
  obtain ⟨tf, htf, regs, hef⟩ := finishCommand_eval m (inputLength d+tm) hm hf'
  refine ⟨tm+tf, ?_, regs, m.stacks 6, m.stacks 9, hem.seq hef, hv, htotal, by omega⟩
  nlinarith [sq_nonneg (inputLength d : ℤ)]

theorem addReuseCommand_eval_total (d : Data) (hd : Ready d) :
    ∃ t ≤ 25000*(inputLength d+3)^2, ∃ regs positive negative,
      Eval addReuseCommand t d (pairState regs positive negative) ∧
      signedValue positive negative =
        signedValue (d.stacks 0) (d.stacks 1) + signedValue (d.stacks 2) (d.stacks 3) ∧
      pairTotal positive negative =
        pairTotal (d.stacks 0) (d.stacks 1) + pairTotal (d.stacks 2) (d.stacks 3) ∧
      positive.length + negative.length ≤ inputLength d+2 := by
  obtain ⟨tm, htm, m, hem, hv, htotal, hl, hf⟩ := addCommand_eval_total d hd
  have hm (j : Fin 15) : (m.stacks j).length ≤ inputLength d+tm := by
    exact (eval_stack_length hem j).trans (Nat.add_le_add_right (total_initial_stack_bound d hd j) tm)
  have hf' (j : Fin 15) (hj : 10 ≤ j.val) : m.stacks j = [] := by
    have hj6 : j ≠ 6 := by intro h; have : j.val = 6 := congrArg Fin.val h; omega
    have hj9 : j ≠ 9 := by intro h; have : j.val = 9 := congrArg Fin.val h; omega
    rw [hf j hj6 hj9, hd j (by omega)]
  obtain ⟨tf, htf, regs, hef⟩ := finishCommand_eval m (inputLength d+tm) hm hf'
  refine ⟨tm+tf, ?_, regs, m.stacks 6, m.stacks 9, hem.seq hef, hv, htotal, hl⟩
  nlinarith [sq_nonneg (inputLength d : ℤ)]


end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
