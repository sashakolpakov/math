import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStages

namespace OAI.Algorithms

/-! The concrete threshold-table phase of the closed setup program. -/

namespace SubexponentialSAT.SubexpSetupPhaseTable

open BitProgram StructuredCalls SubexpSetupProgram

theorem tableFit (c : Config) : tableSlots c < helperSize c := by
  unfold helperSize
  omega

def tableInputs (c : Config) : List (Fin (stackCount c) × Fin (tableSlots c)) :=
  [(persistent c 23,
    SparsificationThresholdTable.inputPort (SparsificationThresholdTable.expressions c.k))]

def tableOutputs (c : Config) : List (Fin (tableSlots c) × Fin (stackCount c)) :=
  List.ofFn (fun i : Fin (thresholdCount c) =>
    (SparsificationThresholdTable.bankPort (SparsificationThresholdTable.expressions c.k) i,
      threshold c i))

def tableOut (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (words : Fin (c.k - 1) → List Bool) : State 8 (tableSlots c) :=
  SparsificationThresholdTable.state (SparsificationThresholdTable.expressions c.k)
    rf (a.stacks (persistent c 23)) [] words

noncomputable def tableResult (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (words : Fin (c.k - 1) → List Bool) : SetupState c :=
  returned c (registerPort (by decide : 8 ≤ 9)) (tableFit c)
    (tableInputs c) (tableOutputs c) a (tableOut c a rf words)

/-- Includes the real input copy, callee trace, output copies, and cleanup. -/
noncomputable def tableCost (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (words : Fin (c.k - 1) → List Bool) (t : ℕ) : ℕ :=
  stageCost c (registerPort (by decide : 8 ≤ 9)) (tableFit c)
    (tableInputs c) (tableOutputs c) a (tableOut c a rf words) t

theorem table_inputs_protected (c : Config) :
    ∀ p ∈ tableInputs c, Protected c p.1 := by
  intro p hp
  obtain rfl := List.mem_singleton.mp hp
  exact persistent_protected c 23

theorem table_outputs_protected (c : Config) :
    ∀ p ∈ tableOutputs c, Protected c p.2 := by
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact threshold_protected c i

theorem table_outputs_nodup (c : Config) :
    ((tableOutputs c).map Prod.snd).Nodup := by
  simp only [tableOutputs, List.map_ofFn]
  apply List.nodup_ofFn_ofInjective
  intro i j h
  have hv := congrArg Fin.val h
  apply Fin.ext
  change helperSize c + i.val = helperSize c + j.val at hv
  omega

theorem table_prepared (c : Config) (a : SetupState c) :
    SubexpSetupStorage.project (registerPort (by decide : 8 ≤ 9))
      (workPort c (tableFit c)) (prepared c (tableFit c) (tableInputs c) a) =
      tableOut c a (fun _ => false) (fun _ => []) := by
  apply prepared_eq c _ _ _ _ _ (table_inputs_protected c)
    (by exact List.nodup_singleton _)
  · intro j
    exact prepared_register c (by decide) (tableFit c) (tableInputs c) a j
  · intro p hp
    obtain rfl := List.mem_singleton.mp hp
    exact SparsificationThresholdTable.state_input _ _ _ _ _
  · intro j hj
    have hne : j ≠ SparsificationThresholdTable.inputPort
        (SparsificationThresholdTable.expressions c.k) :=
      hj (persistent c 23,
        SparsificationThresholdTable.inputPort (SparsificationThresholdTable.expressions c.k))
        (by simp [tableInputs])
    change (SparsificationThresholdTable.state _ _ _ _ _).stacks j = []
    revert hne
    refine Fin.addCases (fun w => ?_) (fun i => ?_) j
    · intro hne
      change Fin.append _
        (fun _ : Fin (thresholdCount c) => ([] : List Bool))
        (Fin.castAdd (thresholdCount c) w) = []
      rw [Fin.append_left]
      have hw : w ≠ SparsificationThresholdTable.workInput
          (SparsificationThresholdTable.expressions c.k) := by
        intro he
        apply hne
        exact congrArg (Fin.castAdd (thresholdCount c)) he
      have hv : w.val ≠ 0 := by
        intro he
        apply hw
        exact Fin.ext he
      simp [ArithmeticExpressionProgram.state, ArithmeticExpressionProgram.inputPort,
        ArithmeticExpressionProgram.outputPort, Function.update_apply, Fin.ext_iff, hv]
    · intro _
      change Fin.append _ (fun _ : Fin (thresholdCount c) => ([] : List Bool))
        (Fin.natAdd (SparsificationThresholdTable.workSlots
          (SparsificationThresholdTable.expressions c.k)) i) = []
      rw [Fin.append_right]

theorem table_result_word (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (words : Fin (c.k - 1) → List Bool) (i : Fin (thresholdCount c)) :
    (tableResult c a rf words).stacks (threshold c i) = words i := by
  have hw := returned_word c (registerPort (by decide : 8 ≤ 9)) (tableFit c)
    (tableInputs c) (tableOutputs c) a (tableOut c a rf words)
    (table_outputs_protected c) (table_outputs_nodup c)
    (SparsificationThresholdTable.bankPort (SparsificationThresholdTable.expressions c.k) i,
      threshold c i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  exact hw.trans (SparsificationThresholdTable.state_bank _ _ _ _ _ _)

theorem table_result_preserves (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (words : Fin (c.k - 1) → List Bool) :
    Preserves c (List.ofFn (threshold c)) a (tableResult c a rf words) := by
  change Preserves c (List.ofFn fun x => threshold c x) a (tableResult c a rf words)
  simpa [tableResult, tableOutputs, Function.comp_def] using
    returned_preserves c (by decide : 8 ≤ 9) (tableFit c)
      (tableInputs c) (tableOutputs c) a (tableOut c a rf words)

theorem table_result_persistent (c : Config) (a : SetupState c) (rf : Fin 8 → Bool)
    (words : Fin (c.k - 1) → List Bool) (i : Fin 32) :
    (tableResult c a rf words).stacks (persistent c i) = a.stacks (persistent c i) := by
  apply returned_frame c _ _ _ _ _ _ _ (persistent_protected c i)
  intro p hp
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hp
  intro he
  have hv := congrArg Fin.val he
  change helperSize c + thresholdCount c + i.val = helperSize c + j.val at hv
  have := j.isLt
  omega

/-- All computation in this phase is the fixed table program and real storage code. -/
theorem table_eval (c : Config) (a : SetupState c) :
    ∃ t rf words,
      t ≤ SparsificationThresholdTable.timeCoeff (SparsificationThresholdTable.expressions c.k) *
        ((a.stacks (persistent c 23)).length + 1)^2 ∧
      Eval (thresholdTable c) (tableCost c a rf words t) a (tableResult c a rf words) ∧
      (∀ i : Fin (thresholdCount c),
        BinaryArithmetic.toNat ((tableResult c a rf words).stacks (threshold c i)) =
          SparsificationConstants.z (BinaryArithmetic.toNat (a.stacks (persistent c 23)))
            (i.val + 2) ∧
        ((tableResult c a rf words).stacks (threshold c i)).length ≤
          ArithmeticExpressionProgram.widthCoeff
            (SparsificationThresholdProgram.thresholdExpr (i.val + 2)) *
              ((a.stacks (persistent c 23)).length + 1)) ∧
      (∑ i, ((tableResult c a rf words).stacks (threshold c i)).length) ≤
        SparsificationThresholdTable.widthCoeff (SparsificationThresholdTable.expressions c.k) *
          ((a.stacks (persistent c 23)).length + 1) ∧
      Preserves c (List.ofFn (threshold c)) a (tableResult c a rf words) := by
  obtain ⟨rf, words, ⟨t, ht, hrun⟩, hv, hl⟩ :=
    SparsificationThresholdTable.thresholdProgram_correct c.k (fun _ => false)
      (a.stacks (persistent c 23))
  refine ⟨t, rf, words, ht, ?_, ?_, ?_, table_result_preserves c a rf words⟩
  · exact stage_eval c (SparsificationThresholdTable.thresholdProgram c.k)
      (registerPort (by decide : 8 ≤ 9)) (registerPort_injective (by decide))
      (tableFit c) (tableInputs c) (tableOutputs c) a
      (tableOut c a (fun _ => false) (fun _ => [])) (tableOut c a rf words)
      (table_inputs_protected c) (table_outputs_protected c) (table_prepared c a) hrun
  · intro i
    rw [table_result_word]
    exact hv i
  · calc
      (∑ i, ((tableResult c a rf words).stacks (threshold c i)).length) =
          ∑ i, (words i).length := by
        apply Finset.sum_congr rfl
        intro i _
        rw [table_result_word]
      _ ≤ SparsificationThresholdTable.widthCoeff
            (SparsificationThresholdTable.expressions c.k) *
          ((a.stacks (persistent c 23)).length + 1) := hl

end SubexponentialSAT.SubexpSetupPhaseTable

end OAI.Algorithms
