import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStages

namespace OAI.Algorithms

/-! Concrete block-size and packed-dimension phases of the closed setup. -/

namespace SubexponentialSAT.SubexpSetupPhaseBlock

noncomputable section

open BitProgram StructuredCalls SubexpSetupProgram

abbrev zeroRegs : Fin 8 → Bool := fun _ => false

def blockInputs (c : Config) : List (Fin (stackCount c) × Fin 22) :=
  [(persistent c 4, 0), (persistent c 16, 1), (persistent c 17, 2)]

def blockOutputs (c : Config) : List (Fin 22 × Fin (stackCount c)) :=
  [(7, persistent c 18), (14, persistent c 20)]

theorem blockFit (c : Config) : 22 < helperSize c := small_fits c (by decide)

def blockLocal (c : Config) (a : SetupState c) : State 8 22 :=
  SubexpBlockParameterProgram.state zeroRegs
    (SubexpBlockParameterProgram.inputWords (a.stacks (persistent c 4))
      (a.stacks (persistent c 16)) (a.stacks (persistent c 17)))

def blockResult (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (w : SubexpBlockParameterProgram.Words) : SetupState c :=
  returned c (registerPort (by decide)) (blockFit c) (blockInputs c) (blockOutputs c) a
    (SubexpBlockParameterProgram.state rf w)

def blockCost (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (w : SubexpBlockParameterProgram.Words) (t : ℕ) : ℕ :=
  stageCost c (registerPort (by decide)) (blockFit c) (blockInputs c) (blockOutputs c) a
    (SubexpBlockParameterProgram.state rf w) t

theorem block_inputs_protected (c : Config) :
    ∀ p ∈ blockInputs c, Protected c p.1 := by
  intro p hp
  simp only [blockInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> exact persistent_protected c _

theorem block_outputs_protected (c : Config) :
    ∀ p ∈ blockOutputs c, Protected c p.2 := by
  intro p hp
  simp only [blockOutputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> exact persistent_protected c _

theorem block_outputs_nodup (c : Config) : ((blockOutputs c).map Prod.snd).Nodup := by
  simp [blockOutputs, persistent, Fin.ext_iff]

theorem block_prepared (c : Config) (a : SetupState c) :
    SubexpSetupStorage.project (registerPort (show 8 ≤ 9 by decide))
      (workPort c (blockFit c)) (prepared c (blockFit c) (blockInputs c) a) =
      blockLocal c a := by
  apply prepared_eq c _ _ _ _ _ (block_inputs_protected c)
    (by simp [blockInputs])
  · intro j
    exact prepared_register c (by decide) (blockFit c) (blockInputs c) a j
  · intro p hp
    simp only [blockInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;>
      simp [blockLocal, SubexpBlockParameterProgram.state,
        SubexpBlockParameterProgram.inputWords]
  · intro j hj
    have h0 : j ≠ 0 := hj (persistent c 4, 0) (by simp [blockInputs])
    have h1 : j ≠ 1 := hj (persistent c 16, 1) (by simp [blockInputs])
    have h2 : j ≠ 2 := hj (persistent c 17, 2) (by simp [blockInputs])
    clear hj
    fin_cases j
    · exact (h0 rfl).elim
    · exact (h1 rfl).elim
    · exact (h2 rfl).elim
    all_goals rfl

theorem block_result_N (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (w : SubexpBlockParameterProgram.Words) :
    (blockResult c a rf w).stacks (persistent c 18) = w 7 := by
  exact returned_word c _ _ _ _ _ _ (block_outputs_protected c)
    (block_outputs_nodup c) (7, persistent c 18) (by simp [blockOutputs])

theorem block_result_Dstar (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (w : SubexpBlockParameterProgram.Words) :
    (blockResult c a rf w).stacks (persistent c 20) = w 14 := by
  exact returned_word c _ _ _ _ _ _ (block_outputs_protected c)
    (block_outputs_nodup c) (14, persistent c 20) (by simp [blockOutputs])

theorem block_result_frame (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (w : SubexpBlockParameterProgram.Words) (i : Fin 32) (h18 : i ≠ 18) (h20 : i ≠ 20) :
    (blockResult c a rf w).stacks (persistent c i) = a.stacks (persistent c i) := by
  apply returned_frame c _ _ _ _ _ _ _ (persistent_protected c i)
  intro p hp
  simp only [blockOutputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> simp_all [persistent, Fin.ext_iff]

theorem block_result_flag (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (w : SubexpBlockParameterProgram.Words) :
    (blockResult c a rf w).regs 15 = a.regs 15 :=
  returned_flag c (by decide) (blockFit c) (blockInputs c) (blockOutputs c) a _

/-- A closed phase: all local computation comes from the concrete block program. -/
theorem block_eval (c : Config) (a : SetupState c) :
    ∃ t rf w,
      t ≤ SubexpBlockParameterProgram.runtimeBound c.k
        (a.stacks (persistent c 4)) (a.stacks (persistent c 16)) (a.stacks (persistent c 17)) + 1 ∧
      SubexpBlockParameterProgram.Output c.k
        (a.stacks (persistent c 4)) (a.stacks (persistent c 16)) (a.stacks (persistent c 17)) w ∧
      Eval (block c) (blockCost c a rf w t) a (blockResult c a rf w) := by
  obtain ⟨rf, w, ho, t, ht, hrun⟩ := SubexpBlockParameterProgram.run_value c.k zeroRegs
    (a.stacks (persistent c 4)) (a.stacks (persistent c 16)) (a.stacks (persistent c 17))
  refine ⟨t, rf, w, ht, ho, ?_⟩
  exact stage_eval c (SubexpBlockParameterProgram.program c.k) (registerPort (by decide))
    (registerPort_injective (by decide)) (blockFit c) (blockInputs c) (blockOutputs c) a
    (blockLocal c a) (SubexpBlockParameterProgram.state rf w)
    (block_inputs_protected c) (block_outputs_protected c) (block_prepared c a) hrun

theorem block_values (k T n : ℕ) (s delta Q : List Bool)
    (w : SubexpBlockParameterProgram.Words)
    (hs : BinaryArithmetic.toNat s = SubexpPackingParameters.s n)
    (hd : BinaryArithmetic.toNat delta = DyadicSchedule.delta k T n)
    (hq : BinaryArithmetic.toNat Q = DyadicSchedule.Q n)
    (ho : SubexpBlockParameterProgram.Output k s delta Q w) :
    BinaryArithmetic.toNat (w 7) = DyadicSchedule.N k T n ∧
      BinaryArithmetic.toNat (w 14) = DyadicSchedule.Dstar k T n := by
  constructor
  · simpa [SubexpBlockParameterProgram.exponentValue, hs, hd, hq,
      DyadicSchedule.N, DyadicSchedule.Q, SubexpParameters.blockSize] using ho.blockSize
  · simpa [SubexpBlockParameterProgram.exponentValue, hs, hd, hq,
      DyadicSchedule.Dstar, DyadicSchedule.N, DyadicSchedule.Q,
      SubexpParameters.blockSize] using ho.blockThreshold

theorem block_scheduled_eval (c : Config) (n : ℕ) (a : SetupState c)
    (hs : BinaryArithmetic.toNat (a.stacks (persistent c 4)) = SubexpPackingParameters.s n)
    (hd : BinaryArithmetic.toNat (a.stacks (persistent c 16)) = DyadicSchedule.delta c.k c.T n)
    (hq : BinaryArithmetic.toNat (a.stacks (persistent c 17)) = DyadicSchedule.Q n) :
    ∃ t rf w,
      t ≤ SubexpBlockParameterProgram.runtimeBound c.k
        (a.stacks (persistent c 4)) (a.stacks (persistent c 16)) (a.stacks (persistent c 17)) + 1 ∧
      Eval (block c) (blockCost c a rf w t) a (blockResult c a rf w) ∧
      BinaryArithmetic.toNat ((blockResult c a rf w).stacks (persistent c 18)) =
        DyadicSchedule.N c.k c.T n ∧
      BinaryArithmetic.toNat ((blockResult c a rf w).stacks (persistent c 20)) =
        DyadicSchedule.Dstar c.k c.T n ∧
      (∀ i : Fin 32, i ≠ 18 → i ≠ 20 →
        (blockResult c a rf w).stacks (persistent c i) = a.stacks (persistent c i)) ∧
      (blockResult c a rf w).regs 15 = a.regs 15 := by
  obtain ⟨t, rf, w, ht, ho, he⟩ := block_eval c a
  obtain ⟨hN, hD⟩ := block_values c.k c.T n _ _ _ w hs hd hq ho
  exact ⟨t, rf, w, ht, he, by simpa only [block_result_N] using hN,
    by simpa only [block_result_Dstar] using hD,
    block_result_frame c a rf w, block_result_flag c a rf w⟩

def dimensionInputs (c : Config) : List (Fin (stackCount c) × Fin 8) :=
  [(persistent c 5, 5), (persistent c 2, 6)]

def dimensionOutputs (c : Config) : List (Fin 8 × Fin (stackCount c)) :=
  [(7, persistent c 19)]

theorem dimensionFit (c : Config) : 8 < helperSize c := small_fits c (by decide)

def dimensionLocal (c : Config) (a : SetupState c) : State 8 8 :=
  SubexpCeilingProgram.inputState zeroRegs
    (a.stacks (persistent c 5)) (a.stacks (persistent c 2))

def dimensionResult (c : Config) (a : SetupState c) (out : State 8 8) : SetupState c :=
  returned c (registerPort (by decide)) (dimensionFit c) (dimensionInputs c)
    (dimensionOutputs c) a out

def dimensionCost (c : Config) (a : SetupState c) (out : State 8 8) (t : ℕ) : ℕ :=
  stageCost c (registerPort (by decide)) (dimensionFit c) (dimensionInputs c)
    (dimensionOutputs c) a out t

theorem dimension_inputs_protected (c : Config) :
    ∀ p ∈ dimensionInputs c, Protected c p.1 := by
  intro p hp
  simp only [dimensionInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> exact persistent_protected c _

theorem dimension_outputs_protected (c : Config) :
    ∀ p ∈ dimensionOutputs c, Protected c p.2 := by
  intro p hp
  simp only [dimensionOutputs, List.mem_singleton] at hp
  subst p
  exact persistent_protected c _

theorem dimension_prepared (c : Config) (a : SetupState c) :
    SubexpSetupStorage.project (registerPort (show 8 ≤ 9 by decide))
      (workPort c (dimensionFit c)) (prepared c (dimensionFit c) (dimensionInputs c) a) =
      dimensionLocal c a := by
  apply prepared_eq c _ _ _ _ _ (dimension_inputs_protected c)
    (by simp [dimensionInputs])
  · intro j
    exact prepared_register c (by decide) (dimensionFit c) (dimensionInputs c) a j
  · intro p hp
    simp only [dimensionInputs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> rfl
  · intro j hj
    have h5 : j ≠ 5 := hj (persistent c 5, 5) (by simp [dimensionInputs])
    have h6 : j ≠ 6 := hj (persistent c 2, 6) (by simp [dimensionInputs])
    fin_cases j <;> simp_all [dimensionLocal, SubexpCeilingProgram.inputState,
      SubexpCeilingProgram.state, ModularQuotientPrograms.quotientStacks]

theorem dimension_result_value (c : Config) (a : SetupState c) (out : State 8 8) :
    (dimensionResult c a out).stacks (persistent c 19) = out.stacks 7 :=
  returned_word c _ _ _ _ _ _ (dimension_outputs_protected c)
    (by simp [dimensionOutputs]) (7, persistent c 19) (by simp [dimensionOutputs])

theorem dimension_result_frame (c : Config) (a : SetupState c) (out : State 8 8)
    (i : Fin 32) (hi : i ≠ 19) :
    (dimensionResult c a out).stacks (persistent c i) = a.stacks (persistent c i) := by
  apply returned_frame c _ _ _ _ _ _ _ (persistent_protected c i)
  intro p hp
  simp only [dimensionOutputs, List.mem_singleton] at hp
  subst p
  simp_all [persistent, Fin.ext_iff]

theorem dimension_result_flag (c : Config) (a : SetupState c) (out : State 8 8) :
    (dimensionResult c a out).regs 15 = a.regs 15 :=
  returned_flag c (by decide) (dimensionFit c) (dimensionInputs c) (dimensionOutputs c) a out

theorem dimension_eval (c : Config) (a : SetupState c)
    (hu : 0 < BinaryArithmetic.toNat (a.stacks (persistent c 5))) :
    ∃ t out,
      t ≤ SubexpCeilingProgram.runtimeBound (a.stacks (persistent c 5)) (a.stacks (persistent c 2)) ∧
      SubexpCeilingProgram.Output (a.stacks (persistent c 5)) (a.stacks (persistent c 2)) out ∧
      Eval (dimension c) (dimensionCost c a out t) a (dimensionResult c a out) := by
  obtain ⟨out, ho, t, ht, hrun⟩ := SubexpCeilingProgram.run_output zeroRegs
    (a.stacks (persistent c 5)) (a.stacks (persistent c 2)) hu
  refine ⟨t, out, ht, ho, ?_⟩
  exact stage_eval c SubexpCeilingProgram.program (registerPort (by decide))
    (registerPort_injective (by decide)) (dimensionFit c) (dimensionInputs c)
    (dimensionOutputs c) a (dimensionLocal c a) out
    (dimension_inputs_protected c) (dimension_outputs_protected c) (dimension_prepared c a) hrun

theorem dimension_value (n : ℕ) (u input : List Bool) (out : State 8 8)
    (hu : BinaryArithmetic.toNat u = SubexpPackingParameters.u n)
    (hn : BinaryArithmetic.toNat input = n) (ho : SubexpCeilingProgram.Output u input out) :
    BinaryArithmetic.toNat (out.stacks 7) = SubexpPackingParameters.D n := by
  simpa only [hu, hn, SubexpPackingParameters.D, SubexpPackingParameters.ell] using ho.1

theorem dimension_scheduled_eval (c : Config) (n : ℕ) (a : SetupState c)
    (hgood : SubexpPackingParameters.GoodInput n)
    (hu : BinaryArithmetic.toNat (a.stacks (persistent c 5)) = SubexpPackingParameters.u n)
    (hn : BinaryArithmetic.toNat (a.stacks (persistent c 2)) = n) :
    ∃ t out,
      t ≤ SubexpCeilingProgram.runtimeBound (a.stacks (persistent c 5)) (a.stacks (persistent c 2)) ∧
      Eval (dimension c) (dimensionCost c a out t) a (dimensionResult c a out) ∧
      BinaryArithmetic.toNat ((dimensionResult c a out).stacks (persistent c 19)) =
        SubexpPackingParameters.D n ∧
      ((dimensionResult c a out).stacks (persistent c 19)).length ≤
        (a.stacks (persistent c 2)).length + 1 ∧
      (∀ i : Fin 32, i ≠ 19 →
        (dimensionResult c a out).stacks (persistent c i) = a.stacks (persistent c i)) ∧
      (dimensionResult c a out).regs 15 = a.regs 15 := by
  have hpos : 0 < BinaryArithmetic.toNat (a.stacks (persistent c 5)) := by
    rw [hu]
    exact SubexpPackingParameters.ell_pos hgood
  obtain ⟨t, out, ht, ho, he⟩ := dimension_eval c a hpos
  have hv := dimension_value n _ _ out hu hn ho
  exact ⟨t, out, ht, he, by simpa only [dimension_result_value] using hv,
    by simpa only [dimension_result_value] using ho.2.1,
    dimension_result_frame c a out, dimension_result_flag c a out⟩

end
end SubexponentialSAT.SubexpSetupPhaseBlock

end OAI.Algorithms
