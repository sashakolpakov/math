import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStages

namespace OAI.Algorithms

/-! The actual tail-operand stage of the growing-parameter setup. -/

namespace SubexponentialSAT.SubexpSetupPhaseTail

noncomputable section

open BitProgram StructuredCalls SubexpSetupProgram

def inputs (c : Config) : List (Fin (stackCount c) × Fin 14) :=
  [(persistent c 25, 0), (persistent c 17, 1), (persistent c 16, 2), (persistent c 4, 3)]

def outputs (c : Config) : List (Fin 14 × Fin (stackCount c)) :=
  [(4, persistent c 26), (5, persistent c 27)]

theorem fits (c : Config) : 14 < helperSize c := small_fits c (by decide)

def localState (c : Config) (a : SetupState c) : State 8 14 :=
  ⟨fun _ => false, ![a.stacks (persistent c 25), a.stacks (persistent c 17),
    a.stacks (persistent c 16), a.stacks (persistent c 4),
    [], [], [], [], [], [], [], [], [], []]⟩

def localResult (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (square tail : List Bool) : State 8 14 :=
  ⟨rf, Function.update (Function.update (localState c a).stacks 4 square) 5 tail⟩

def result (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (square tail : List Bool) : SetupState c :=
  returned c (registerPort (by decide)) (fits c) (inputs c) (outputs c) a
    (localResult c a rf square tail)

def cost (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (square tail : List Bool) (t : ℕ) : ℕ :=
  stageCost c (registerPort (by decide)) (fits c) (inputs c) (outputs c) a
    (localResult c a rf square tail) t

theorem inputs_protected (c : Config) : ∀ p ∈ inputs c, Protected c p.1 := by
  intro p hp
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> exact persistent_protected c _

theorem outputs_protected (c : Config) : ∀ p ∈ outputs c, Protected c p.2 := by
  intro p hp
  simp only [outputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> exact persistent_protected c _

theorem outputs_nodup (c : Config) : ((outputs c).map Prod.snd).Nodup := by
  simp [outputs, persistent, Fin.ext_iff]

theorem prepared_state (c : Config) (a : SetupState c) :
    SubexpSetupStorage.project (registerPort (show 8 ≤ 9 by decide))
      (workPort c (fits c)) (prepared c (fits c) (inputs c) a) = localState c a := by
  apply prepared_eq c _ _ _ _ _ (inputs_protected c) (by simp [inputs])
  · intro j
    exact prepared_register c (by decide) (fits c) (inputs c) a j
  · intro p hp
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> rfl
  · intro j hj
    have h0 : j ≠ 0 := hj (persistent c 25, 0) (by simp [inputs])
    have h1 : j ≠ 1 := hj (persistent c 17, 1) (by simp [inputs])
    have h2 : j ≠ 2 := hj (persistent c 16, 2) (by simp [inputs])
    have h3 : j ≠ 3 := hj (persistent c 4, 3) (by simp [inputs])
    fin_cases j <;> simp_all [localState]

theorem local_ready (c : Config) (a : SetupState c) :
    SubexpGuardTailProgram.Ready (localState c a) := by
  intro i hi
  fin_cases i <;> simp_all [localState]

theorem result_square (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (square tail : List Bool) : (result c a rf square tail).stacks (persistent c 26) = square := by
  exact returned_word c _ _ _ _ _ _ (outputs_protected c) (outputs_nodup c)
    (4, persistent c 26) (by simp [outputs])

theorem result_tail (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (square tail : List Bool) : (result c a rf square tail).stacks (persistent c 27) = tail := by
  exact returned_word c _ _ _ _ _ _ (outputs_protected c) (outputs_nodup c)
    (5, persistent c 27) (by simp [outputs])

theorem result_frame (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (square tail : List Bool) (i : Fin 32) (h26 : i ≠ 26) (h27 : i ≠ 27) :
    (result c a rf square tail).stacks (persistent c i) = a.stacks (persistent c i) := by
  apply returned_frame c _ _ _ _ _ _ _ (persistent_protected c i)
  intro p hp
  simp only [outputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp_all [persistent, Fin.ext_iff]

theorem result_flag (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (square tail : List Bool) : (result c a rf square tail).regs 15 = a.regs 15 :=
  returned_flag c (by decide) (fits c) (inputs c) (outputs c) a _

theorem eval (c : Config) (a : SetupState c) :
    ∃ t rf square tail,
      t ≤ 2000 * SubexpGuardTailProgram.width (localState c a) ^ 2 + 1 ∧
      Eval (tailOperands c) (cost c a rf square tail t) a (result c a rf square tail) ∧
      BinaryArithmetic.toNat square = BinaryArithmetic.toNat (a.stacks (persistent c 25)) ^ 2 ∧
      BinaryArithmetic.toNat tail = 16 * BinaryArithmetic.toNat (a.stacks (persistent c 17)) *
        BinaryArithmetic.toNat (a.stacks (persistent c 16)) *
        BinaryArithmetic.toNat (a.stacks (persistent c 4)) ∧
      square.length ≤ 2 * (a.stacks (persistent c 25)).length + 1 ∧
      tail.length ≤ (a.stacks (persistent c 17)).length + (a.stacks (persistent c 16)).length +
        (a.stacks (persistent c 4)).length + 8 := by
  obtain ⟨t, rf, square, tail, hrun, hv1, hv2, hl1, hl2, ht⟩ :=
    SubexpGuardTailProgram.command_trace (localState c a) (local_ready c a)
  refine ⟨t + 1, rf, square, tail, Nat.add_le_add_right ht 1, ?_, hv1, hv2, hl1, hl2⟩
  exact stage_eval c SubexpGuardTailProgram.program (registerPort (by decide))
    (registerPort_injective (by decide)) (fits c) (inputs c) (outputs c) a
    (localState c a) (localResult c a rf square tail)
    (inputs_protected c) (outputs_protected c) (prepared_state c a) hrun

theorem scheduled_eval (c : Config) (n : ℕ) (a : SetupState c)
    (hR : BinaryArithmetic.toNat (a.stacks (persistent c 25)) = DyadicSchedule.R c.k c.T n)
    (hQ : BinaryArithmetic.toNat (a.stacks (persistent c 17)) = DyadicSchedule.Q n)
    (hd : BinaryArithmetic.toNat (a.stacks (persistent c 16)) = DyadicSchedule.delta c.k c.T n)
    (hs : BinaryArithmetic.toNat (a.stacks (persistent c 4)) = SubexpPackingParameters.s n) :
    ∃ t rf square tail,
      t ≤ 2000 * SubexpGuardTailProgram.width (localState c a) ^ 2 + 1 ∧
      Eval (tailOperands c) (cost c a rf square tail t) a (result c a rf square tail) ∧
      BinaryArithmetic.toNat ((result c a rf square tail).stacks (persistent c 26)) =
        DyadicSchedule.R c.k c.T n ^ 2 ∧
      BinaryArithmetic.toNat ((result c a rf square tail).stacks (persistent c 27)) =
        16 * DyadicSchedule.Q n * DyadicSchedule.delta c.k c.T n * SubexpPackingParameters.s n ∧
      (∀ i : Fin 32, i ≠ 26 → i ≠ 27 →
        (result c a rf square tail).stacks (persistent c i) = a.stacks (persistent c i)) ∧
      (result c a rf square tail).regs 15 = a.regs 15 := by
  obtain ⟨t, rf, square, tail, ht, he, hv1, hv2, _, _⟩ := eval c a
  exact ⟨t, rf, square, tail, ht, he,
    by simpa only [result_square, hR] using hv1,
    by simpa only [result_tail, hQ, hd, hs] using hv2,
    result_frame c a rf square tail, result_flag c a rf square tail⟩

end
end SubexponentialSAT.SubexpSetupPhaseTail

end OAI.Algorithms
