import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingProgramArithmetic

namespace OAI.Algorithms

/-! Exact signed arithmetic for minor enumeration. Integers are represented as
pairs of natural binary words. No modular arithmetic, integer oracle, or
parameter-dependent instruction table is used. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic

abbrev Data := State 8 15

def signedValue (positive negative : List Bool) : ℤ :=
  (BinaryArithmetic.toNat positive : ℤ) - (BinaryArithmetic.toNat negative : ℤ)

def inputLength (d : Data) : ℕ :=
  (d.stacks 0).length + (d.stacks 1).length +
  (d.stacks 2).length + (d.stacks 3).length

def Ready (d : Data) : Prop := ∀ j : Fin 15, 4 ≤ j.val → d.stacks j = []

def positivePorts : Fin 12 → Fin 15 := ![0, 2, 1, 3, 4, 5, 6, 10, 11, 12, 13, 14]
def negativePorts : Fin 12 → Fin 15 := ![0, 3, 1, 2, 7, 8, 9, 10, 11, 12, 13, 14]

theorem positivePorts_injective : Function.Injective positivePorts := by decide
theorem negativePorts_injective : Function.Injective negativePorts := by decide

abbrev scoreCall (ports : Fin 12 → Fin 15) : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram PackingProgram.weightedScoreProgram id ports)

def readScore (ports : Fin 12 → Fin 15) (d : Data) : PackingProgram.ArithmeticData :=
  ⟨d.regs, fun j => d.stacks (ports j)⟩

private theorem scoreCall_eval (ports : Fin 12 → Fin 15)
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

/-- Inputs 0,1 represent the first integer and 2,3 the second. Outputs 6,9
represent their product. Ports 4,5,7,8 contain intermediate products; 10--14
are restored empty. All input words are preserved. -/
abbrev multiplyCommand : Cmd 8 15 :=
  .seq (scoreCall positivePorts) (scoreCall negativePorts)

def multiplyProgram := compiled multiplyCommand 0 6

theorem multiplyCommand_eval (d : Data) (hd : Ready d) :
    ∃ t ≤ 600 * (inputLength d + 3)^2 + 2, ∃ e : Data,
      Eval multiplyCommand t d e ∧
      signedValue (e.stacks 6) (e.stacks 9) =
        signedValue (d.stacks 0) (d.stacks 1) *
          signedValue (d.stacks 2) (d.stacks 3) ∧
      (e.stacks 6).length ≤ inputLength d + 3 ∧
      (e.stacks 9).length ≤ inputLength d + 3 ∧
      (∀ j : Fin 15, j.val < 4 ∨ 10 ≤ j.val → e.stacks j = d.stacks j) := by
  have hp : PackingProgram.arithmeticReady (readScore positivePorts d) := by
    intro j hj
    have hj' : 4 ≤ (positivePorts j).val := by
      fin_cases j <;> norm_num [positivePorts] at *
    exact hd _ hj'
  obtain ⟨tp, htp, middle, he1, hv1, hl1, hf1⟩ :=
    scoreCall_eval positivePorts positivePorts_injective d hp
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
    scoreCall_eval negativePorts negativePorts_injective middle hn
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
    out, he1.seq he2, ?_, ?_, ?_, ?_⟩
  · simp only [signedValue, hpout]
    simp [PackingProgram.weightedScoreValue, readScore, positivePorts] at hv1
    simp [PackingProgram.weightedScoreValue, readScore, negativePorts,
      hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide)] at hv2
    rw [hv1, hv2]
    push_cast
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

theorem multiplyProgram_runsIn (d : Data) (hd : Ready d) :
    ∃ e : Data,
      RunsIn multiplyProgram (600 * (inputLength d + 3)^2 + 3)
        (d.withPC (some multiplyProgram.entry)) (e.withPC none) ∧
      signedValue (e.stacks 6) (e.stacks 9) =
        signedValue (d.stacks 0) (d.stacks 1) * signedValue (d.stacks 2) (d.stacks 3) := by
  obtain ⟨t, ht, e, he, hv, _⟩ := multiplyCommand_eval d hd
  exact ⟨e, ⟨t+1, by omega, compiled_halt_trace he 0 6⟩, hv⟩

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
