import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainInvariant
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayout
import OAI.Algorithms.SubexponentialSAT.SubexpMainAssignmentPorts
import OAI.Algorithms.SubexponentialSAT.ModularArithmetic

namespace OAI.Algorithms

/-!
# Numerical values retained from the actual Main boot

The word equalities in `Stored` refer to the output of the actual setup run.
This module transfers its numerical postconditions to the current caller and
to the layout procedure's physical input ports. No word is required to be a
canonical binary representation: the modulus width follows from its value.
-/

namespace SubexponentialSAT.SubexpMainParameterValues

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupProgram
open SubexpMainInvariant (Stored ParameterPort)

attribute [local simp] Fin.coe_ofNat_eq_mod

variable {cfg : Config} {er n B : ℕ} {setup : SetupState cfg}
variable {a : MainState er (mainExtraStacks cfg)}

theorem projected_parameter (h : Stored cfg setup B a) (i : Fin 32)
    (hi : ParameterPort i) :
    ((mainProcedure cfg er).project a).stacks (SubexpSetupProgram.persistent cfg i) =
      setup.stacks (SubexpSetupProgram.persistent cfg i) :=
  (main_project_word cfg er a i).trans (h.parameters i hi)

theorem scalarValues_of_stored (h : Stored cfg setup B a)
    (hs : ScalarValues cfg n setup) :
    ScalarValues cfg n ((mainProcedure cfg er).project a) := by
  have hv (i : Fin 32) (hi : ParameterPort i) :=
    congrArg BinaryArithmetic.toNat (projected_parameter h i hi)
  constructor
  · exact (hv 6 (by simp [ParameterPort])).trans hs.prime
  · exact (hv 23 (by simp [ParameterPort])).trans hs.M
  · exact (hv 24 (by simp [ParameterPort])).trans hs.B
  · exact (hv 16 (by simp [ParameterPort])).trans hs.delta
  · exact (hv 17 (by simp [ParameterPort])).trans hs.Q
  · exact (hv 25 (by simp [ParameterPort])).trans hs.R
  · exact (hv 18 (by simp [ParameterPort])).trans hs.N
  · exact (hv 19 (by simp [ParameterPort])).trans hs.D
  · exact (hv 20 (by simp [ParameterPort])).trans hs.Dstar
  · exact (hv 26 (by simp [ParameterPort])).trans hs.square
  · exact (hv 27 (by simp [ParameterPort])).trans hs.tail
  · exact (hv 21 (by simp [ParameterPort])).trans hs.colors
  · exact (hv 22 (by simp [ParameterPort])).trans hs.precision
  · exact (hv 29 (by simp [ParameterPort])).trans hs.inverseExponent

theorem thresholdValues_of_stored (h : Stored cfg setup B a)
    (hs : ThresholdValues cfg n setup) :
    ThresholdValues cfg n ((mainProcedure cfg er).project a) := by
  intro i
  change BinaryArithmetic.toNat (a.stacks (mainStack cfg (threshold cfg i))) = _
  exact (congrArg BinaryArithmetic.toNat (h.thresholds i)).trans (hs i)

variable {hr : 32 ≤ workRegs er} {F : SAT.CNF (Fin n)}

/-- Retained frontend words are recovered from the same actual boot run. -/
theorem retained_word (run : SubexpMainBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) (i : Fin 32)
    (hi : ParameterPort i) (hret : Retained i) :
    a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i) =
      run.before.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) i) :=
  (h.parameters i hi).trans
    ((main_install_word cfg er run.before run.setupOutput i).symm.trans
      (run.setupPost.retained i hret))

theorem variableCount (run : SubexpMainBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    BinaryArithmetic.toNat
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 2)) = n := by
  have hw := retained_word run h 2 (by simp [ParameterPort])
    ⟨by decide, Or.inl (by decide)⟩
  exact (congrArg BinaryArithmetic.toNat hw).trans
    (SubexpMainBootPrefix.facts_of_execution F run.prefixTrace).variableCount

theorem scale (run : SubexpMainBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    BinaryArithmetic.toNat
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 4)) =
        SubexpPackingParameters.s n := by
  have hw := retained_word run h 4 (by simp [ParameterPort])
    ⟨by decide, Or.inl (by decide)⟩
  exact (congrArg BinaryArithmetic.toNat hw).trans
    (SubexpMainBootPrefix.facts_of_execution F run.prefixTrace).scale

theorem capacity (run : SubexpMainBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    BinaryArithmetic.toNat
      (a.stacks (SubexpMainProgram.persistent (mainExtraStacks cfg) 5)) =
        SubexpPackingParameters.u n := by
  have hw := retained_word run h 5 (by simp [ParameterPort])
    ⟨by decide, Or.inl (by decide)⟩
  exact (congrArg BinaryArithmetic.toNat hw).trans
    (SubexpMainBootPrefix.facts_of_execution F run.prefixTrace).capacity

theorem scalarValues (run : SubexpMainBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    ScalarValues cfg n ((mainProcedure cfg er).project a) :=
  scalarValues_of_stored h run.setupPost.scalar

theorem thresholdValues (run : SubexpMainBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    ThresholdValues cfg n ((mainProcedure cfg er).project a) :=
  thresholdValues_of_stored h run.setupPost.thresholds

theorem threshold (run : SubexpMainBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) (i : Fin (thresholdCount cfg)) :
    BinaryArithmetic.toNat (a.stacks (mainStack cfg (threshold cfg i))) =
      SparsificationConstants.z (DyadicSchedule.M cfg.T n) (i.val + 2) :=
  (congrArg BinaryArithmetic.toNat (h.thresholds i)).trans (run.setupPost.thresholds i)

section LayoutPorts

variable {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) (current : MainState er es)

theorem sourceInputs_n_word :
    (SubexpMainLayout.Factors.sourceInputs alloc current).counts.n =
      current.stacks (SubexpMainProgram.persistent es 2) :=
  congrArg current.stacks (SubexpMainLayout.Factors.stackMap_input alloc 0)

theorem sourceInputs_ell_word :
    (SubexpMainLayout.Factors.sourceInputs alloc current).counts.ell =
      current.stacks (SubexpMainProgram.persistent es 5) :=
  congrArg current.stacks (SubexpMainLayout.Factors.stackMap_input alloc 1)

theorem sourceInputs_modulus_word :
    (SubexpMainLayout.Factors.sourceInputs alloc current).counts.modulus =
      current.stacks (SubexpMainProgram.persistent es 6) :=
  congrArg current.stacks (SubexpMainLayout.Factors.stackMap_input alloc 2)

theorem sourceInputs_dimension_word :
    (SubexpMainLayout.Factors.sourceInputs alloc current).counts.dimension =
      current.stacks (SubexpMainProgram.persistent es 19) :=
  congrArg current.stacks (SubexpMainLayout.Factors.stackMap_input alloc 3)

theorem sourceInputs_leaf :
    (SubexpMainLayout.Factors.sourceInputs alloc current).leaf =
      current.stacks (SubexpMainProgram.persistent es 9) :=
  congrArg current.stacks (SubexpMainLayout.Factors.stackMap_input alloc 4)

end LayoutPorts

variable (alloc : SubexpLayoutPorts.Allocation (mainExtraStacks cfg))

theorem sourceInputs_variableCount (run : SubexpMainBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    SubexpLayoutConstruction.variableCount (SubexpMainLayout.Factors.sourceInputs alloc a) = n := by
  unfold SubexpLayoutConstruction.variableCount
  rw [sourceInputs_n_word, CounterPrograms.value_eq_toNat]
  exact variableCount run h

theorem sourceInputs_ell (run : SubexpMainBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell =
      SubexpPackingParameters.ell n := by
  rw [sourceInputs_ell_word, CounterPrograms.value_eq_toNat]
  exact capacity run h

theorem sourceInputs_modulus (run : SubexpMainBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    BinaryArithmetic.toNat (SubexpMainLayout.Factors.sourceInputs alloc a).counts.modulus =
      SubexpPackingParameters.p n := by
  rw [sourceInputs_modulus_word]
  simpa only [main_project_word] using (scalarValues run h).prime

theorem sourceInputs_dimension (run : SubexpMainBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a) =
      SubexpPackingParameters.D n := by
  unfold SubexpLayoutConstruction.dimension
  rw [sourceInputs_dimension_word, CounterPrograms.value_eq_toNat]
  simpa only [main_project_word] using (scalarValues run h).D

theorem sourceInputs_chunk_count (run : SubexpMainBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) :
    SubexpLayoutConstruction.dimension (SubexpMainLayout.Factors.sourceInputs alloc a) =
      ChunkPartition.count
        (SubexpLayoutConstruction.variableCount (SubexpMainLayout.Factors.sourceInputs alloc a))
        (CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell) := by
  rw [sourceInputs_dimension alloc run h, sourceInputs_variableCount alloc run h,
    sourceInputs_ell alloc run h]
  rfl

theorem sourceInputs_capacity (run : SubexpMainBoot.Run cfg hr F)
    (h : Stored cfg run.setupOutput B a) (hg : SubexpPackingParameters.GoodInput n) :
    2 ^ CounterPrograms.value (SubexpMainLayout.Factors.sourceInputs alloc a).counts.ell ≤
      SubexpPackingParameters.p n := by
  rw [sourceInputs_ell alloc run h]
  exact (SubexpPackingParameters.p_lower hg).le

theorem sourceInputs_width (run : SubexpMainBoot.Run cfg hr F)
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

theorem sourceInputs_metadata (run : SubexpMainBoot.Run cfg hr F)
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
theorem sourceInputs_ready (run : SubexpMainBoot.Run cfg hr F)
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

end SubexponentialSAT.SubexpMainParameterValues

end OAI.Algorithms
