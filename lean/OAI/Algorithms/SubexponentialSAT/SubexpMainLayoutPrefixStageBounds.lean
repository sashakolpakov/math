import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLayoutWordBounds
import OAI.Algorithms.SubexponentialSAT.SubexpMainAssignment
import OAI.Algorithms.SubexponentialSAT.SubexpMainUniversalTypes
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentFrontendBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingTupleBounds

namespace OAI.Algorithms

/-! Closed numeric bounds for the actual assignment and universal-type
stages. Only input words and numerical parameters occur in the envelopes;
no intermediate byte length or execution cost is supplied as a premise. -/

namespace SubexponentialSAT.SubexpMainLayoutPrefixStageBounds

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupStorage Subexp
open SubexpMainLayoutWordBounds
open SubexpPreparedSetupCalls (StackBound)
open scoped BigOperators

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem master_relevant {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) (i : Fin 32) :
    RelevantPort es (SubexpLayoutPorts.master alloc i) := by
  left
  rw [SubexpLayoutPorts.master_val]
  omega

theorem assignment_relevant {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) (i : Fin 63) :
    RelevantPort es (SubexpMainAssignment.stackMap alloc i) := by
  unfold SubexpMainAssignment.stackMap
  split
  · left; simp only [SubexpMainAssignment.lowPort, SubexpLayoutPorts.ordinary]; omega
  · split
    · right
      refine ⟨_, rfl, Or.inl ?_⟩
      generalize hj : (⟨i.val - 51, by omega⟩ : Fin 4) = j
      fin_cases j <;> norm_num [SubexpMainAssignment.metadataIndex, SubexpMainInvariant.ParameterPort]
    · exact master_relevant alloc _

theorem universal_relevant {es : ℕ} (alloc : SubexpLayoutPorts.Allocation es) (i : Fin 13) :
    RelevantPort es (SubexpMainUniversalTypes.stackMap alloc i) := by
  unfold SubexpMainUniversalTypes.stackMap
  split
  · left; simp only [SubexpLayoutPorts.ordinary]; omega
  · exact master_relevant alloc _

private theorem count_loop_bound (rs : List (List Bool)) :
    SubexpSunflowerProgram.CountRecords.loopSteps rs ≤
      3 * (Encoding.encodeList id rs).length + 2 := by
  have h := ProgramEncoding.encodeRecords_length rs
  change (Encoding.encodeList id rs).length = _ at h
  unfold SubexpSunflowerProgram.CountRecords.loopSteps
  omega

theorem countBudget_bound (scopes : List (List ℕ)) :
    SubexpAssignmentSetup.countBudget scopes ≤
      10 * (SubexpPlanAlphabetBase.scopeBytes scopes).length + 8 := by
  have h := count_loop_bound (SubexpAssignmentSetup.scopeRecords scopes)
  rw [SubexpAssignmentSetup.scopeRecords_encode] at h
  unfold SubexpAssignmentSetup.countBudget SubexpScopeCountSetup.countBudget
  rw [SubexpAssignmentSetup.scopeRecords_encode]
  omega

private theorem unary_bound (bits : List Bool) (X : ℕ)
    (hX : 1 ≤ X) (hlen : bits.length + 1 ≤ X)
    (hvalue : CounterPrograms.value bits + 1 ≤ X) :
    SubexpAssignmentSetup.unaryBudget bits ≤ 44 * X ^ 2 := by
  have hprod : (CounterPrograms.value bits + 1) * (bits.length + 1) ≤ X ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul hvalue hlen
  have hlin : X ≤ X ^ 2 := AssignmentFrontendBounds.le_power hX (by decide)
  unfold SubexpAssignmentSetup.unaryBudget CounterConversions.runtimeBound
  nlinarith only [hprod, hlin, hlen, hX]

def assignmentCoefficient : ℕ := 201 * (AssignmentFrontendBounds.coefficient + 2000) + 20000

private theorem assignment_finish_arithmetic (W Z C P B : ℕ)
    (hp : P ≤ C * Z) (hb : B ≤ 63 * W) (hw : W ≤ Z) (hz : 1 ≤ Z) :
    P + 200 * (B + P + 2) + 1 ≤ (201 * C + 20000) * Z := by
  nlinarith only [hp, hb, hw, hz]

theorem assignment_local_bound (a : SubexpAssignmentSetup.Data) (W r Q Δ D : ℕ)
    (scopes : List (List ℕ)) (ha : StackBound a W) (hr : 0 < r)
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (hv : ∀ i, CounterPrograms.value (a.stacks (SubexpAssignmentSetup.source i)) =
      (![r, Q, Δ, D] : Fin 4 → ℕ) i) :
    SubexpAssignmentStaging.runtimeBound a r Q Δ D scopes ≤
      assignmentCoefficient * (W + AssignmentFrontendBounds.sourceSize r Q Δ D scopes + 1) ^ 60 := by
  let S := AssignmentFrontendBounds.sourceSize r Q Δ D scopes
  let X := W + S + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hW : W + 1 ≤ X := by dsimp [X]; omega
  have hS : S ≤ X := by dsimp [X]; omega
  have h2 : X ≤ X ^ 2 := AssignmentFrontendBounds.le_power hX (by decide)
  have h60 : X ≤ X ^ 60 := AssignmentFrontendBounds.le_power hX (by decide)
  have h260 : X ^ 2 ≤ X ^ 60 := Nat.pow_le_pow_right hX (by decide)
  have h160 : 1 ≤ X ^ 60 := hX.trans h60
  have hsum : r + Q + Δ + D ≤ S := by dsimp [S, AssignmentFrontendBounds.sourceSize]; omega
  have hbytes : (SubexpPlanAlphabetBase.scopeBytes scopes).length ≤ S := by
    dsimp [S, AssignmentFrontendBounds.sourceSize]; omega
  have hu (i : Fin 4) : SubexpAssignmentSetup.unaryBudget
      (a.stacks (SubexpAssignmentSetup.source i)) ≤ 44 * X ^ 2 := by
    apply unary_bound _ X hX ((Nat.add_le_add_right (ha _) 1).trans hW)
    rw [hv i]
    have hi : (![r, Q, Δ, D] : Fin 4 → ℕ) i ≤ r + Q + Δ + D := by
      fin_cases i <;> simp <;> omega
    dsimp [X]
    omega
  have hclear := SubexpPreparedSetupCalls.clearManyCost_le SubexpAssignmentSetup.clearedPorts a ha
  have hclearLen : SubexpAssignmentSetup.clearedPorts.length = 58 := by
    simp [SubexpAssignmentSetup.clearedPorts, SubexpAssignmentSetup.scratch]
  rw [hclearLen] at hclear
  have hc := countBudget_bound scopes
  have hprep : SubexpAssignmentSetup.preparationBudget a scopes ≤ 1000 * X ^ 2 := by
    have h0 := hu 0; have h1 := hu 1; have h2' := hu 2; have h3 := hu 3
    unfold SubexpAssignmentSetup.preparationBudget SubexpAssignmentSetup.seedBudget
    omega
  have hfront := AssignmentFrontendBounds.sourceBudget_le r Q Δ D scopes hr hd
  have hfront' : AssignmentFrontendProgram.sourceBudget r Q Δ D scopes ≤
      AssignmentFrontendBounds.coefficient * X ^ 60 :=
    hfront.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hS 60))
  have hp : SubexpAssignmentStaging.prefixBudget a r Q Δ D scopes ≤
      (AssignmentFrontendBounds.coefficient + 2000) * X ^ 60 := by
    unfold SubexpAssignmentStaging.prefixBudget
    have ht : 4 * (7 * (r + Q + Δ + D) + 5) ≤ 1000 * X ^ 60 := by omega
    calc
      _ ≤ 1000 * X ^ 60 + 1000 * X ^ 60 +
          AssignmentFrontendBounds.coefficient * X ^ 60 := by
        exact Nat.add_le_add (Nat.add_le_add (hprep.trans (Nat.mul_le_mul_left _ h260)) ht) hfront'
      _ = _ := by rw [Nat.add_mul]; omega
  have hw : SubexpAssignmentStaging.wordBound a ≤ 63 * W := by
    unfold SubexpAssignmentStaging.wordBound
    calc
      _ ≤ ∑ _i : Fin 63, W := Finset.sum_le_sum (fun i _ => ha i)
      _ = _ := by simp
  change SubexpAssignmentStaging.runtimeBound a r Q Δ D scopes ≤ assignmentCoefficient * X ^ 60
  unfold SubexpAssignmentStaging.runtimeBound assignmentCoefficient
  exact assignment_finish_arithmetic W (X ^ 60) _ _ _ hp hw (by omega) h160

theorem assignment_bound {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (W r Q Δ D : ℕ) (scopes : List (List ℕ))
    (ha : RelevantWordBound W a) (hr : 0 < r)
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ)
    (hv : ∀ i, CounterPrograms.value (a.stacks (persistent es (SubexpMainAssignment.metadataIndex i))) =
      (![r, Q, Δ, D] : Fin 4 → ℕ) i) :
    SubexpMainAssignment.runtimeBound alloc a r Q Δ D scopes ≤
      assignmentCoefficient * (W + AssignmentFrontendBounds.sourceSize r Q Δ D scopes + 1) ^ 60 := by
  apply assignment_local_bound _ W r Q Δ D scopes
  · intro i
    exact ha _ (assignment_relevant alloc i)
  · exact hr
  · exact hd
  · intro i
    change CounterPrograms.value (a.stacks
      (SubexpMainAssignment.stackMap alloc (SubexpAssignmentSetup.source i))) = _
    rw [SubexpMainAssignment.stackMap_metadata]
    exact hv i

def universalSize (r Q Δ : ℕ) : ℕ := r + Q + Δ + MulticolorTypes.blockSize r Q Δ + 1

theorem universal_generator_bound (r Q Δ : ℕ) (hr : 0 < r) :
    UniversalTypeProgram.budget (AssignmentAlphabetSemantics.wordBytes r Q) Δ ≤
      10000 * universalSize r Q Δ ^ 5 := by
  let S := universalSize r Q Δ
  have hS : 1 ≤ S := by dsimp [S, universalSize]; omega
  have hrS : r ≤ S := by dsimp [S, universalSize]; omega
  have hQS : Q ≤ S := by dsimp [S, universalSize]; omega
  have hd : Δ + 2 ≤ 2 * S := by dsimp [S, universalSize]; omega
  have hN : MulticolorTypes.blockSize r Q Δ + 1 ≤ 2 * S := by dsimp [S, universalSize]; omega
  have hqr : Q * r ≤ S ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hQS hrS
  have h3 : 1 ≤ S ^ 3 := Nat.one_le_pow _ _ hS
  have h5 : 1 ≤ S ^ 5 := Nat.one_le_pow _ _ hS
  have hwidth : (Δ + 2) * (Q * r) + 1 ≤ 3 * S ^ 3 := by
    calc
      _ ≤ (2 * S) * S ^ 2 + 1 := Nat.add_le_add_right (Nat.mul_le_mul hd hqr) 1
      _ ≤ _ := by nlinarith only [h3]
  have hc := PackingTupleBounds.generated_powerCost_le
    (AssignmentAlphabetSemantics.wordBytes r Q) (Δ + 1) (Q * r)
    (fun x hx => (AssignmentAlphabetSemantics.wordBytes_width hr x hx).le)
  rw [AssignmentAlphabetSemantics.wordBytes_length, ← Nat.pow_mul] at hc
  change TupleProgram.powerCost _ _ _ ≤
    800 * (Δ + 1 + 1) * (MulticolorTypes.blockSize r Q Δ + 1) * ((Δ + 1 + 1) * (Q * r) + 1) at hc
  have hb : TupleProgram.powerCost (AssignmentAlphabetSemantics.wordBytes r Q) (Δ + 1) [[]] ≤
      9600 * S ^ 5 := by
    calc
      _ ≤ 800 * (2 * S) * (2 * S) * (3 * S ^ 3) := hc.trans (by gcongr)
      _ = _ := by ring
  change _ ≤ 10000 * S ^ 5
  unfold UniversalTypeProgram.budget
  omega

theorem universal_prepare_bound (a : SubexpMainUniversalTypes.Staging.Data) (W : ℕ)
    (ha : StackBound a W) :
    prepareCost 12 SubexpMainUniversalTypes.Staging.work
      SubexpMainUniversalTypes.Staging.inputs a ≤ 50 * (W + 1) := by
  have h0 := SubexpPreparedSetupCalls.clearManyCost_le [12] a ha
  have h1 := SubexpPreparedSetupCalls.clearManyCost_le SubexpMainUniversalTypes.Staging.work
    (clearManyState [12] a) (SubexpPreparedSetupCalls.clearMany_bound [12] a ha)
  have h2 := SubexpPreparedSetupCalls.copyManyCost_le SubexpMainUniversalTypes.Staging.inputs
    (beforeCopies 12 SubexpMainUniversalTypes.Staging.work a)
    (fun p _ => SubexpPreparedSetupCalls.beforeCopies_bound _ _ a ha p.1) (by
      intro p hp q hq
      simp only [SubexpMainUniversalTypes.Staging.inputs, List.mem_cons, List.not_mem_nil,
        or_false] at hp hq
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> decide)
  have hw : SubexpMainUniversalTypes.Staging.work.length = 9 := by
    simp [SubexpMainUniversalTypes.Staging.work]
  have hi : SubexpMainUniversalTypes.Staging.inputs.length = 2 := rfl
  rw [hw] at h1
  rw [hi] at h2
  simp only [List.length_singleton, one_mul] at h0
  unfold prepareCost
  omega

theorem universal_local_bound (a : SubexpMainUniversalTypes.Staging.Data) (W r Q Δ : ℕ)
    (ha : StackBound a W) (hr : 0 < r) :
    SubexpMainUniversalTypes.Staging.runtimeBound a r Q Δ ≤
      2000000 * (W + universalSize r Q Δ + 1) ^ 5 := by
  let X := W + universalSize r Q Δ + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hW : W + 1 ≤ X := by dsimp [X]; omega
  have hS : universalSize r Q Δ ≤ X := by dsimp [X]; omega
  have h5 : X ≤ X ^ 5 := AssignmentFrontendBounds.le_power hX (by decide)
  have h15 : 1 ≤ X ^ 5 := hX.trans h5
  have hp := universal_prepare_bound a W ha
  have hg := (universal_generator_bound r Q Δ hr).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hS 5))
  have hb : SubexpMainUniversalTypes.Staging.prefixBudget a r Q Δ ≤ 10050 * X ^ 5 := by
    unfold SubexpMainUniversalTypes.Staging.prefixBudget
    omega
  have hw : SubexpMainUniversalTypes.Staging.wordBound a ≤ 13 * W := by
    unfold SubexpMainUniversalTypes.Staging.wordBound
    calc
      _ ≤ ∑ _i : Fin 13, W := Finset.sum_le_sum (fun i _ => ha i)
      _ = _ := by simp
  change _ ≤ 2000000 * X ^ 5
  unfold SubexpMainUniversalTypes.Staging.runtimeBound
  omega

theorem universal_bound {er es : ℕ} (alloc : SubexpLayoutPorts.Allocation es)
    (a : MainState er es) (W r Q Δ : ℕ) (ha : RelevantWordBound W a) (hr : 0 < r) :
    SubexpMainUniversalTypes.runtimeBound alloc a r Q Δ ≤
      2000000 * (W + universalSize r Q Δ + 1) ^ 5 := by
  apply universal_local_bound _ W r Q Δ _ hr
  intro i
  exact ha _ (universal_relevant alloc i)

end SubexponentialSAT.SubexpMainLayoutPrefixStageBounds

end OAI.Algorithms
