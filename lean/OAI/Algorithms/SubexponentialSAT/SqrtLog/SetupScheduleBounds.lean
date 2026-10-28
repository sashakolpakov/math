import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.SetupSchedule

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Schedule

open BitProgram StructuredCalls SubexpSetupProgram SubexpSetupStorage

/-- The storage wrapper is paid even when incoming work and output words are
dirty. Its constant depends neither on the formula nor on the integer input. -/
theorem bounded_eval (c : Config) (B : ℕ) (a : SetupState c) (ha : WordBound B a) :
    ∃ t b, Eval (command c) t a b ∧ t ≤ 100000000000000000*(B+1)^3 ∧
      WordBound (100000000000000000*(B+1)^3) b := by
  have hstart : WordBound B (start c a) := by
    intro i
    exact prepared_wordBound c (fits c) (inputs c) a B
      (inputs_protected c) (inputs_nodup c) ha (workPort c (fits c) i)
  obtain ⟨u,out,he,_,_,_,_,_,_,hu⟩ := Execution.ScheduleLocal.command_eval (start c a) (start_ready c a)
  have hN := hstart 18
  have hO := hstart 21
  have hx : 1 ≤ (B+1)^3 := Nat.one_le_pow _ _ (by omega)
  have hB : B ≤ (B+1)^3 := by
    exact (Nat.le_succ B).trans (Nat.le_self_pow (by decide) (B+1))
  have hsum : ((start c a).stacks 18).length + ((start c a).stacks 21).length + 1 ≤ 2*(B+1) := by omega
  have hp := Nat.pow_le_pow_left hsum 3
  have huc := hu.trans (Execution.ScheduleLocal.bound_cubic _ _)
  have htime : u ≤ 320000000000000*(B+1)^3 := by
    calc
      u ≤ 40000000000000 * (((start c a).stacks 18).length + ((start c a).stacks 21).length + 1)^3 := huc
      _ ≤ 40000000000000*(2*(B+1))^3 := Nat.mul_le_mul_left _ hp
      _ = _ := by ring
  let K := 320000000000001*(B+1)^3
  have haK : WordBound K a := fun i => (ha i).trans (by dsimp [K]; omega)
  have hout : WordBound K out := by
    have hh := SubexpSetupBoundSpec.eval_wordBound hstart he
    intro i
    exact (hh i).trans (by dsimp [K]; omega)
  have hstorage := stageCost_le c (registerPort (by decide : 8 ≤ 9)) (fits c)
    (inputs c) (outputs c) a out (u+1) K
    (inputs_protected c) (outputs_protected c) (inputs_nodup c) (outputs_nodup c) haK hout
  have hret := returned_wordBound c (registerPort (by decide : 8 ≤ 9)) (fits c)
    (inputs c) (outputs c) a out K
    (inputs_protected c) (outputs_protected c) (inputs_nodup c) (outputs_nodup c) haK hout
  have ht : cost c a out u ≤ 100000000000000000*(B+1)^3 := by
    have hov := storageOverhead_linear 22 2 3 K
    change storageOverhead 22 2 3 K ≤ 197*(K+1) at hov
    change cost c a out u ≤ (u+1)+storageOverhead 22 (inputs c).length (outputs c).length K at hstorage
    simp only [inputs,outputs,List.length_cons,List.length_nil] at hstorage
    change cost c a out u ≤ (u+1)+storageOverhead 22 2 3 K at hstorage
    dsimp [K] at hov hstorage
    omega
  refine ⟨_,result c a out,call_eval c a out he,ht,?_⟩
  intro i
  exact (hret i).trans (by dsimp [K]; omega)

theorem polynomial_envelope (c : Config) : PolynomialEnvelope (command c) := by
  refine ⟨100000000000000000,3,by decide,by decide,?_⟩
  intro B a t b ha he
  exact SubexpSetupBoundSpec.bounds_of_witness (persistent c 0) (bounded_eval c B a ha) he

end SubexponentialSAT.SqrtLog.Setup.Schedule

end OAI.Algorithms
