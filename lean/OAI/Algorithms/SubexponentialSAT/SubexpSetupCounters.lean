import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStages

namespace OAI.Algorithms

/-! Actual increment/decrement stages for the two exponent metadata words. -/

noncomputable section

namespace SubexponentialSAT.SubexpSetupProgram

open BitProgram StructuredCalls SubexpSetupStorage BinaryArithmetic

def counterStage (c : Config) (increment : Bool) (source target : Fin 32) : SetupCmd c :=
  stage c (CounterPrograms.rippleProgram increment) (registerPort (by decide))
    (small_fits c (by decide)) [(persistent c source, 0)] [(0, persistent c target)]

def counterOut (increment : Bool) (xs : List Bool) : State 3 2 :=
  StructuredProgram.ioState 0 (CounterPrograms.ripple increment xs)

def counterResult (c : Config) (increment : Bool) (source target : Fin 32)
    (a : SetupState c) : SetupState c :=
  returned c (registerPort (show 3 ≤ 9 by decide)) (small_fits c (by decide))
    [(persistent c source, 0)] [(0, persistent c target)] a
    (counterOut increment (a.stacks (persistent c source)))

def counterBound (c : Config) (increment : Bool) (source target : Fin 32)
    (a : SetupState c) : ℕ :=
  stageCost c (registerPort (show 3 ≤ 9 by decide)) (small_fits c (by decide))
    [(persistent c source, 0)] [(0, persistent c target)] a
    (counterOut increment (a.stacks (persistent c source)))
    (8 * (a.stacks (persistent c source)).length + 8)

private theorem counter_prepared (c : Config) (source : Fin 32) (a : SetupState c) :
    project (registerPort (show 3 ≤ 9 by decide)) (workPort c (small_fits c (by decide : 2 ≤ 32)))
      (prepared c (small_fits c (by decide : 2 ≤ 32)) [(persistent c source, 0)] a) =
      (StructuredProgram.ioState 0 (a.stacks (persistent c source)) : State 3 2) := by
  apply prepared_eq c _ _ _ _ _ (by simp) (by simp)
  · intro j
    exact prepared_register c (by decide) _ _ a j
  · intro p hp
    obtain rfl := List.mem_singleton.mp hp
    simp []
  · intro j hj
    have hne : j ≠ 0 := hj (persistent c source, 0) (by simp)
    simp [ hne]

theorem counterStage_eval (c : Config) (increment : Bool) (source target : Fin 32)
    (a : SetupState c) :
    ∃ t, t ≤ counterBound c increment source target a ∧
      Eval (counterStage c increment source target) t a (counterResult c increment source target a) ∧
      (counterResult c increment source target a).stacks (persistent c target) =
        CounterPrograms.ripple increment (a.stacks (persistent c source)) ∧
      Preserves c [persistent c target] a (counterResult c increment source target a) := by
  obtain ⟨t, ht, htrace⟩ := CounterPrograms.ripple_terminal_runs increment (a.stacks (persistent c source))
  have he := stage_eval c (CounterPrograms.rippleProgram increment)
    (registerPort (show 3 ≤ 9 by decide)) (registerPort_injective (by decide))
    (small_fits c (by decide : 2 ≤ 32)) [(persistent c source, 0)] [(0, persistent c target)]
    a (StructuredProgram.ioState 0 (a.stacks (persistent c source)))
    (counterOut increment (a.stacks (persistent c source))) (by simp) (by simp)
    (counter_prepared c source a)
    htrace
  refine ⟨_, stageCost_mono c _ _ _ _ _ _ ht, he, ?_, ?_⟩
  · exact returned_word c _ _ _ _ _ _ (by simp) (by simp)
      (0, persistent c target) (by simp)
  · exact returned_preserves c (by decide) _ _ _ a _

theorem precision_eval (c : Config) (a : SetupState c) :
    ∃ t b, t ≤ counterBound c true 19 22 a ∧ Eval (precision c) t a b ∧
      BinaryArithmetic.toNat (b.stacks (persistent c 22)) = BinaryArithmetic.toNat (a.stacks (persistent c 19)) + 1 ∧
      (b.stacks (persistent c 22)).length ≤ (a.stacks (persistent c 19)).length + 1 ∧
      Preserves c [persistent c 22] a b := by
  obtain ⟨t, ht, he, hw, hf⟩ := counterStage_eval c true 19 22 a
  refine ⟨t, _, ht, he, ?_, ?_, hf⟩
  · rw [hw]
    simpa only [CounterPrograms.value_eq_toNat] using
      CounterPrograms.value_increment (a.stacks (persistent c 19))
  · rw [hw]
    exact CounterPrograms.ripple_length_le true _

theorem inverseExponent_eval (c : Config) (a : SetupState c)
    (hpos : 0 < BinaryArithmetic.toNat (a.stacks (persistent c 17))) :
    ∃ t b, t ≤ counterBound c false 17 29 a ∧ Eval (inverseExponent c) t a b ∧
      BinaryArithmetic.toNat (b.stacks (persistent c 29)) = BinaryArithmetic.toNat (a.stacks (persistent c 17)) - 1 ∧
      (b.stacks (persistent c 29)).length = (a.stacks (persistent c 17)).length ∧
      Preserves c [persistent c 29] a b := by
  have hp : 0 < CounterPrograms.value (a.stacks (persistent c 17)) := by
    simpa only [CounterPrograms.value_eq_toNat] using hpos
  obtain ⟨t, ht, he, hw, hf⟩ := counterStage_eval c false 17 29 a
  refine ⟨t, _, ht, he, ?_, ?_, hf⟩
  · rw [hw]
    have hv := CounterPrograms.value_decrement hp
    simp only [CounterPrograms.value_eq_toNat] at hv
    omega
  · rw [hw]
    exact CounterPrograms.decrement_length hp

theorem inverseExponent_schedule (c : Config) (n : ℕ) (a : SetupState c)
    (hQ : BinaryArithmetic.toNat (a.stacks (persistent c 17)) = DyadicSchedule.Q n) :
    ∃ t b, Eval (inverseExponent c) t a b ∧
      BinaryArithmetic.toNat (b.stacks (persistent c 29)) = SubexpPackingParameters.p n ^ 4 - 2 ∧
      Preserves c [persistent c 29] a b := by
  obtain ⟨t, b, _, he, hv, _, hf⟩ := inverseExponent_eval c a (by rw [hQ]; exact DyadicSchedule.Q_pos n)
  refine ⟨t, b, he, ?_, hf⟩
  rw [hv, hQ]
  change (SubexpPackingParameters.p n ^ 4 - 1) - 1 = _
  omega

end SubexponentialSAT.SubexpSetupProgram

end

end OAI.Algorithms
