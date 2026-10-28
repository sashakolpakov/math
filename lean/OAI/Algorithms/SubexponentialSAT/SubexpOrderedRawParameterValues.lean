import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainParameterValues
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawBoot

namespace OAI.Algorithms

/-! Numerical facts at the actual ordered-input boot. The physical words
and setup output come from this run; no canonical boot is constructed. -/

namespace SubexponentialSAT.SubexpOrderedRawParameterValues

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupProgram
open SubexpMainInvariant (Stored ParameterPort)
open SubexpMainParameterValues (scalarValues_of_stored thresholdValues_of_stored
  sourceInputs_n_word sourceInputs_ell_word sourceInputs_modulus_word
  sourceInputs_dimension_word sourceInputs_leaf)

attribute [local simp] Fin.coe_ofNat_eq_mod

variable {cfg : Config} {er n B : ℕ} {a : MainState er (mainExtraStacks cfg)}

variable {hr : 32 ≤ workRegs er} {F : SubexpOrderedRawPrefix.Formula n}

/-- Retained frontend words are recovered from the same actual boot run. -/
theorem retained_word (run : SubexpOrderedRawBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) (i : Fin 32)
    (hi : ParameterPort i) (hret : Retained i) :
    a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i) =
      run.before.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i) :=
  (h.parameters i hi).trans
    ((main_install_word cfg er run.before run.setupOutput i).symm.trans
      (run.setupPost.retained i hret))

theorem variableCount (run : SubexpOrderedRawBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    BinaryArithmetic.toNat
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 2)) = n := by
  have hw := retained_word run h 2 (by simp [ParameterPort])
    ⟨by decide, Or.inl (by decide)⟩
  exact (congrArg BinaryArithmetic.toNat hw).trans
    (SubexpOrderedRawPrefix.facts_of_execution F run.prefixTrace).variableCount

theorem scale (run : SubexpOrderedRawBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    BinaryArithmetic.toNat
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 4)) =
        SubexpPackingParameters.s n := by
  have hw := retained_word run h 4 (by simp [ParameterPort])
    ⟨by decide, Or.inl (by decide)⟩
  exact (congrArg BinaryArithmetic.toNat hw).trans
    (SubexpOrderedRawPrefix.facts_of_execution F run.prefixTrace).scale

theorem capacity (run : SubexpOrderedRawBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    BinaryArithmetic.toNat
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 5)) =
        SubexpPackingParameters.u n := by
  have hw := retained_word run h 5 (by simp [ParameterPort])
    ⟨by decide, Or.inl (by decide)⟩
  exact (congrArg BinaryArithmetic.toNat hw).trans
    (SubexpOrderedRawPrefix.facts_of_execution F run.prefixTrace).capacity

theorem scalarValues (run : SubexpOrderedRawBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    ScalarValues cfg n ((mainProcedure cfg er).project a) :=
  scalarValues_of_stored h run.setupPost.scalar

theorem thresholdValues (run : SubexpOrderedRawBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    ThresholdValues cfg n ((mainProcedure cfg er).project a) :=
  thresholdValues_of_stored h run.setupPost.thresholds

theorem threshold (run : SubexpOrderedRawBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) (i : Fin (thresholdCount cfg)) :
    BinaryArithmetic.toNat (a.stacks (mainStack cfg (threshold cfg i))) =
      SparsificationConstants.z (DyadicSchedule.M cfg.T n) (i.val + 2) :=
  (congrArg BinaryArithmetic.toNat (h.thresholds i)).trans (run.setupPost.thresholds i)

variable (alloc : SubexpLayoutPorts.Allocation (mainExtraStacks cfg))

theorem sourceInputs_variableCount (run : SubexpOrderedRawBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    SubexpLayoutConstruction.variableCount (SubexpMainLayout.Factors.sourceInputs alloc a) = n := by
  unfold SubexpLayoutConstruction.variableCount
  rw [sourceInputs_n_word, CounterPrograms.value_eq_toNat]
  exact variableCount run h

theorem sourceInputs_ell (run : SubexpOrderedRawBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell =
      SubexpPackingParameters.ell n := by
  rw [sourceInputs_ell_word, CounterPrograms.value_eq_toNat]
  exact capacity run h

theorem sourceInputs_modulus (run : SubexpOrderedRawBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    BinaryArithmetic.toNat (SubexpMainLayout.Factors.sourceInputs alloc a).counts.modulus =
      SubexpPackingParameters.p n := by
  rw [sourceInputs_modulus_word]
  simpa only [main_project_word] using (scalarValues run h).prime

theorem sourceInputs_dimension (run : SubexpOrderedRawBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a) =
      SubexpPackingParameters.D n := by
  unfold SubexpLayoutConstruction.dimension
  rw [sourceInputs_dimension_word, CounterPrograms.value_eq_toNat]
  simpa only [main_project_word] using (scalarValues run h).D

theorem sourceInputs_chunk_count (run : SubexpOrderedRawBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a) =
      ChunkPartition.count
        (SubexpLayoutConstruction.variableCount (SubexpMainLayout.Factors.sourceInputs alloc a))
        (CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell) := by
  rw [sourceInputs_dimension alloc run h, sourceInputs_variableCount alloc run h,
    sourceInputs_ell alloc run h]
  rfl

theorem sourceInputs_capacity (run : SubexpOrderedRawBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) (hg : SubexpPackingParameters.GoodInput n) :
    2 ^ CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell ≤
      SubexpPackingParameters.p n := by
  rw [sourceInputs_ell alloc run h]
  exact (SubexpPackingParameters.p_lower hg).le

theorem sourceInputs_width (run : SubexpOrderedRawBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) (hg : SubexpPackingParameters.GoodInput n) :
    CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell ≤
      (SubexpMainLayout.Factors.sourceInputs alloc a).counts.modulus.length := by
  have hl := ModularArithmetic.toNat_lt_pow_length
    (SubexpMainLayout.Factors.sourceInputs alloc a).counts.modulus
  rw [sourceInputs_modulus alloc run h] at hl
  have hc := sourceInputs_capacity alloc run h hg
  by_contra hn
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ))
    (show (SubexpMainLayout.Factors.sourceInputs alloc a).counts.modulus.length ≤
      CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell by omega)
  omega

theorem sourceInputs_metadata (run : SubexpOrderedRawBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    ∀ i : Fin 4, CounterPrograms.value
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg)
        (SubexpMainAssignment.metadataIndex i))) =
      (![SubexpPackingParameters.r n, DyadicSchedule.Q n, DyadicSchedule.delta cfg.k cfg.T n,
        SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)] :
          Fin 4 → ℕ) i := by
  have hs := scalarValues run h
  intro i
  fin_cases i
  · change CounterPrograms.value (a.stacks (SubexpMainProgram.persistent _ 21)) =
      SubexpPackingParameters.r n
    simpa only [CounterPrograms.value_eq_toNat, main_project_word] using hs.colors
  · change CounterPrograms.value (a.stacks (SubexpMainProgram.persistent _ 17)) =
      DyadicSchedule.Q n
    simpa only [CounterPrograms.value_eq_toNat, main_project_word] using hs.Q
  · change CounterPrograms.value (a.stacks (SubexpMainProgram.persistent _ 16)) =
      DyadicSchedule.delta cfg.k cfg.T n
    simpa only [CounterPrograms.value_eq_toNat, main_project_word] using hs.delta
  · change CounterPrograms.value (a.stacks (SubexpMainProgram.persistent _ 19)) =
      SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a)
    rw [sourceInputs_dimension alloc run h, CounterPrograms.value_eq_toNat]
    simpa only [main_project_word] using hs.D

/-- All scalar preconditions of the layout prefix follow from the retained
actual setup state; the leaf-specific width/occurrence facts remain separate. -/
theorem sourceInputs_ready (run : SubexpOrderedRawBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) (hg : SubexpPackingParameters.GoodInput n) :
    let x := SubexpMainLayout.Factors.sourceInputs alloc a
    0 < CounterPrograms.value x.counts.ell ∧
    CounterPrograms.value x.counts.ell ≤ x.counts.modulus.length ∧
    0 < BinaryArithmetic.toNat x.counts.modulus ∧
    SubexpLayoutConstruction.dimension x = ChunkPartition.count
      (SubexpLayoutConstruction.variableCount x) (CounterPrograms.value x.counts.ell) ∧
    2 ^ CounterPrograms.value x.counts.ell ≤ SubexpPackingParameters.p n ∧
    1 + CounterPrograms.value x.counts.ell * DyadicSchedule.B cfg.k cfg.T n ≤
      DyadicSchedule.delta cfg.k cfg.T n := by
  dsimp only
  refine ⟨?_, sourceInputs_width alloc run h hg, ?_,
    sourceInputs_chunk_count alloc run h, sourceInputs_capacity alloc run h hg, ?_⟩
  · rw [sourceInputs_ell alloc run h]
    exact SubexpPackingParameters.ell_pos hg
  · rw [sourceInputs_modulus alloc run h]
    exact (by decide : 0 < (2 : ℕ)).trans (SubexpPackingParameters.p_gt_two n)
  · rw [sourceInputs_ell alloc run h]
    exact Nat.le_refl _

end SubexponentialSAT.SubexpOrderedRawParameterValues

end OAI.Algorithms
