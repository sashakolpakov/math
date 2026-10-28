import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupControl
import OAI.Algorithms.SubexponentialSAT.SubexpSetupCounters
import OAI.Algorithms.SubexponentialSAT.SubexpSetupInvariant
import OAI.Algorithms.SubexponentialSAT.SubexpSetupPhaseArithmetic
import OAI.Algorithms.SubexponentialSAT.SubexpSetupPhaseBlock
import OAI.Algorithms.SubexponentialSAT.SubexpSetupPhaseTail
import OAI.Algorithms.SubexponentialSAT.SubexpSetupPhaseTable

namespace OAI.Algorithms

/-! Correctness of the closed, post-prefix numerical setup. Every execution
below is assembled from the proved traces of the named finite programs. -/

namespace SubexponentialSAT.SubexpSetupProgram

open BitProgram StructuredCalls BinaryArithmetic SubexpSetupStorage
open SubexpSetupPhaseArithmetic

private theorem known_one (c : Config) (n : ℕ) (a : SetupState c) (i : Fin 32)
    (h : wordValue c a i = wanted c n i) : Known c n [i] a := by
  intro j hj
  obtain rfl := List.mem_singleton.mp hj
  exact h

private theorem known_two (c : Config) (n : ℕ) (a : SetupState c) (i j : Fin 32)
    (hi : wordValue c a i = wanted c n i) (hj : wordValue c a j = wanted c n j) :
    Known c n [i,j] a := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hi
  · obtain rfl := List.mem_singleton.mp hq
    exact hj

theorem numericSetup_eval_with_Mword (c : Config) (n : ℕ) (a : SetupState c)
    (hgood : SubexpPackingParameters.GoodInput n) (hk : Known c n initialKnown a) :
    ∃ t b, Eval (numericSetup c) t a b ∧ Known c n finalKnown b ∧ RetainedFrame c a b ∧
      b.stacks (persistent c 23) =
        SparsificationBudgetProgram.outputWord c.T (SubexpPackingParameters.s n) := by
  obtain ⟨t1, _, e1, v1, _, p1⟩ := selectM_schedule c n a (hk 4 (by decide))
  let a1 := selectResult c a
  have f1 : ScalarFrame c [23] a a1 := preserves_scalarFrame c [23] a a1 p1
  have k1 := known_extend c n initialKnown [23] a a1 hk f1 (known_one c n a1 23 v1)
  have pf1 := scalarFrame_retained c [23] a a1 f1 (by simp [Retained])

  obtain ⟨t2, rf2, w2, _, e2, v2, _, p2⟩ := occurrence_schedule c n a1 (k1 23 (by simp))
  let a2 := occurrenceResult c a1 rf2 w2
  have f2 : ScalarFrame c [24] a1 a2 := preserves_scalarFrame c [24] a1 a2 p2
  have k2 := known_extend c n _ [24] a1 a2 k1 f2 (known_one c n a2 24 v2)
  have pf2 := retainedFrame_trans c pf1 (scalarFrame_retained c [24] a1 a2 f2 (by simp [Retained]))

  obtain ⟨t3, rf3, w3, _, e3, v3, _, p3⟩ := incidence_schedule c n a2
    (k2 5 (by simp [initialKnown])) (k2 24 (by simp))
  let a3 := incidenceResult c a2 rf3 w3
  have f3 : ScalarFrame c [16] a2 a3 := preserves_scalarFrame c [16] a2 a3 p3
  have k3 := known_extend c n _ [16] a2 a3 k2 f3 (known_one c n a3 16 v3)
  have pf3 := retainedFrame_trans c pf2 (scalarFrame_retained c [16] a2 a3 f3 (by simp [Retained]))

  obtain ⟨t4, out4, _, e4, v4, _, p4⟩ := prime_schedule c n a3 (k3 5 (by simp [initialKnown]))
  let a4 := primeResult c a3 out4
  have f4 : ScalarFrame c [6] a3 a4 := preserves_scalarFrame c [6] a3 a4 p4
  have k4 := known_extend c n _ [6] a3 a4 k3 f4 (known_one c n a4 6 v4)
  have pf4 := retainedFrame_trans c pf3 (scalarFrame_retained c [6] a3 a4 f4 (by simp [Retained]))

  obtain ⟨t5, out5, _, e5, v5Q, v5R, _, _, _, p5⟩ := field_schedule c n a4
    (k4 6 (by simp)) (k4 16 (by simp))
  let a5 := fieldResult c a4 out5
  have f5 : ScalarFrame c [17,25] a4 a5 := preserves_scalarFrame c [17,25] a4 a5 p5
  have k5 := known_extend c n _ [17,25] a4 a5 k4 f5 (known_two c n a5 17 25 v5Q v5R)
  have pf5 := retainedFrame_trans c pf4 (scalarFrame_retained c [17,25] a4 a5 f5 (by simp [Retained]))

  obtain ⟨t6, out6, _, e6, v6, _, p6, _⟩ :=
    SubexpSetupPhaseBlock.dimension_scheduled_eval c n a5 hgood
      (k5 5 (by simp [initialKnown])) (k5 2 (by simp [initialKnown]))
  let a6 := SubexpSetupPhaseBlock.dimensionResult c a5 out6
  have f6 : ScalarFrame c [19] a5 a6 := by
    intro i hi
    exact p6 i (by simpa only [List.mem_singleton] using hi)
  have k6 := known_extend c n _ [19] a5 a6 k5 f6 (known_one c n a6 19 v6)
  have pf6 := retainedFrame_trans c pf5 (scalarFrame_retained c [19] a5 a6 f6 (by simp [Retained]))

  obtain ⟨t7, rf7, w7, _, e7, v7N, v7D, p7, _⟩ :=
    SubexpSetupPhaseBlock.block_scheduled_eval c n a6
      (k6 4 (by simp [initialKnown])) (k6 16 (by simp)) (k6 17 (by simp))
  let a7 := SubexpSetupPhaseBlock.blockResult c a6 rf7 w7
  have f7 : ScalarFrame c [18,20] a6 a7 := by
    intro i hi
    have h : i ≠ 18 ∧ i ≠ 20 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using hi
    exact p7 i h.1 h.2
  have k7 := known_extend c n _ [18,20] a6 a7 k6 f7
    (known_two c n a7 18 20 (v7N.trans (wanted_blockSize c n).symm) v7D)
  have pf7 := retainedFrame_trans c pf6 (scalarFrame_retained c [18,20] a6 a7 f7 (by simp [Retained]))

  obtain ⟨t8, rf8, square8, tail8, _, e8, v8S, v8T, p8, _⟩ :=
    SubexpSetupPhaseTail.scheduled_eval c n a7 (k7 25 (by simp)) (k7 17 (by simp))
      (k7 16 (by simp)) (k7 4 (by simp [initialKnown]))
  let a8 := SubexpSetupPhaseTail.result c a7 rf8 square8 tail8
  have f8 : ScalarFrame c [26,27] a7 a8 := by
    intro i hi
    have h : i ≠ 26 ∧ i ≠ 27 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using hi
    exact p8 i h.1 h.2
  have k8 := known_extend c n _ [26,27] a7 a8 k7 f8 (known_two c n a8 26 27 v8S v8T)
  have pf8 := retainedFrame_trans c pf7 (scalarFrame_retained c [26,27] a7 a8 f8 (by simp [Retained]))

  obtain ⟨t9, a9, _, e9, v9, _, p9⟩ := precision_eval c a8
  have v9' : wordValue c a9 22 = wanted c n 22 := by
    change BinaryArithmetic.toNat (a9.stacks (persistent c 22)) = SubexpPackingParameters.D n + 1
    rw [v9]
    exact congrArg (fun x : ℕ => x + 1) (k8 19 (by simp))
  have f9 : ScalarFrame c [22] a8 a9 := preserves_scalarFrame c [22] a8 a9 p9
  have k9 := known_extend c n _ [22] a8 a9 k8 f9 (known_one c n a9 22 v9')
  have pf9 := retainedFrame_trans c pf8 (scalarFrame_retained c [22] a8 a9 f9 (by simp [Retained]))

  obtain ⟨t10, a10, e10, v10, p10⟩ := inverseExponent_schedule c n a9 (k9 17 (by simp))
  have f10 : ScalarFrame c [29] a9 a10 := preserves_scalarFrame c [29] a9 a10 p10
  have k10 := known_extend c n _ [29] a9 a10 k9 f10 (known_one c n a10 29 v10)
  have pf10 := retainedFrame_trans c pf9 (scalarFrame_retained c [29] a9 a10 f10 (by simp [Retained]))

  obtain ⟨t11, a11, e11, w11, p11⟩ := colors_eval c a10
  have v11 : wordValue c a11 21 = wanted c n 21 :=
    (congrArg BinaryArithmetic.toNat w11).trans (k10 4 (by simp [initialKnown]))
  have f11 : ScalarFrame c [21] a10 a11 := preserves_scalarFrame c [21] a10 a11 p11
  have k11 := known_extend c n _ [21] a10 a11 k10 f11 (known_one c n a11 21 v11)
  have pf11 := retainedFrame_trans c pf10 (scalarFrame_retained c [21] a10 a11 f11 (by simp [Retained]))

  obtain ⟨t12, a12, e12, v12, p12⟩ := cutoff_eval c a11
  have f12 : ScalarFrame c [28] a11 a12 := preserves_scalarFrame c [28] a11 a12 p12
  have k12 := known_extend c n _ [28] a11 a12 k11 f12 (known_one c n a12 28 v12)
  have pf12 := retainedFrame_trans c pf11 (scalarFrame_retained c [28] a11 a12 f12 (by simp [Retained]))

  have eall := Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 (Eval.seq e5 (Eval.seq e6
    (Eval.seq e7 (Eval.seq e8 (Eval.seq e9 (Eval.seq e10 (Eval.seq e11 e12))))))))))
  have hm : a12.stacks (persistent c 23) = a1.stacks (persistent c 23) := by
    calc
      a12.stacks (persistent c 23) = a11.stacks (persistent c 23) := f12 23 (by decide)
      _ = a10.stacks (persistent c 23) := f11 23 (by decide)
      _ = a9.stacks (persistent c 23) := f10 23 (by decide)
      _ = a8.stacks (persistent c 23) := f9 23 (by decide)
      _ = a7.stacks (persistent c 23) := f8 23 (by decide)
      _ = a6.stacks (persistent c 23) := f7 23 (by decide)
      _ = a5.stacks (persistent c 23) := f6 23 (by decide)
      _ = a4.stacks (persistent c 23) := f5 23 (by decide)
      _ = a3.stacks (persistent c 23) := f4 23 (by decide)
      _ = a2.stacks (persistent c 23) := f3 23 (by decide)
      _ = a1.stacks (persistent c 23) := f2 23 (by decide)
  refine ⟨_, a12, eall, ?_, pf12, ?_⟩
  · simpa only [initialKnown, finalKnown, List.cons_append, List.nil_append] using k12
  · exact hm.trans (selectResult_word_schedule c n a (hk 4 (by decide)))

theorem numericSetup_eval (c : Config) (n : ℕ) (a : SetupState c)
    (hgood : SubexpPackingParameters.GoodInput n) (hk : Known c n initialKnown a) :
    ∃ t b, Eval (numericSetup c) t a b ∧ Known c n finalKnown b ∧ RetainedFrame c a b := by
  obtain ⟨t, b, he, hvalues, hframe, _⟩ := numericSetup_eval_with_Mword c n a hgood hk
  exact ⟨t, b, he, hvalues, hframe⟩

/-- The persistent control word is the actual producer's bit string, including
its padding convention, for every execution of the numerical setup. -/
theorem numericSetup_Mword (c : Config) (n : ℕ) {a b : SetupState c} {t : ℕ}
    (hgood : SubexpPackingParameters.GoodInput n) (hk : Known c n initialKnown a)
    (he : Eval (numericSetup c) t a b) :
    b.stacks (persistent c 23) =
      SparsificationBudgetProgram.outputWord c.T (SubexpPackingParameters.s n) := by
  obtain ⟨t', b', he', _, _, hw⟩ := numericSetup_eval_with_Mword c n a hgood hk
  have hb := SubexpPrimeProgram.eval_result_unique he he' (persistent c 0) (persistent c 0)
  exact (congrArg (fun state : SetupState c => state.stacks (persistent c 23)) hb).trans hw

def ThresholdValues (c : Config) (n : ℕ) (a : SetupState c) : Prop :=
  ∀ i : Fin (thresholdCount c), BinaryArithmetic.toNat (a.stacks (threshold c i)) =
    SparsificationConstants.z (DyadicSchedule.M c.T n) (i.val + 2)

theorem scalarSetup_eval (c : Config) (n : ℕ) (a : SetupState c)
    (hgood : SubexpPackingParameters.GoodInput n) (hk : Known c n initialKnown a) :
    ∃ t b, Eval (scalarSetup c) t a b ∧ Known c n finalKnown b ∧
      ThresholdValues c n b ∧ (b.regs 15 = true ↔ DyadicSchedule.Ready c.k c.T n) ∧
      RetainedFrame c a b := by
  obtain ⟨tn, an, en, kn, fn⟩ := numericSetup_eval c n a hgood hk
  obtain ⟨tt, rf, words, _, et, vt, _, _⟩ := SubexpSetupPhaseTable.table_eval c an
  let atab := SubexpSetupPhaseTable.tableResult c an rf words
  have ft : ∀ i : Fin 32, atab.stacks (persistent c i) = an.stacks (persistent c i) :=
    SubexpSetupPhaseTable.table_result_persistent c an rf words
  have kt := known_frame c n finalKnown an atab kn ft
  have tv : ThresholdValues c n atab := by
    intro i
    exact (vt i).1.trans (congrArg (fun x => SparsificationConstants.z x (i.val + 2))
      (kn 23 (by simp [finalKnown])))
  obtain ⟨tg, b, eg, vb, fg⟩ := readyGuard_eval c n atab
    (kt 4 (by simp [finalKnown])) (kt 28 (by simp [finalKnown])) (kt 19 (by simp [finalKnown])) (kt 20 (by simp [finalKnown]))
    (kt 26 (by simp [finalKnown])) (kt 27 (by simp [finalKnown]))
  refine ⟨_, b, .seq en (.seq et eg), ?_, ?_, vb, ?_⟩
  · exact known_frame c n finalKnown atab b kt (fun i => fg _ (persistent_protected c i))
  · intro i
    exact (congrArg BinaryArithmetic.toNat (fg _ (threshold_protected c i))).trans (tv i)
  · intro i hi
    exact (fg _ (persistent_protected c i)).trans ((ft i).trans (fn i hi))

theorem scalarCommand_eval (c : Config) (n : ℕ) (a : SetupState c)
    (hk : Known c n initialKnown a) :
    ∃ t b, Eval (scalarCommand c) t a b ∧
      (b.regs 15 = true ↔ DyadicSchedule.Ready c.k c.T n) ∧
      (SubexpPackingParameters.GoodInput n → Known c n finalKnown b ∧ ThresholdValues c n b) ∧
      RetainedFrame c a b := by
  obtain ⟨te, ae, ee, ve, fe⟩ := early_eval c a
  have ke := known_frame c n initialKnown a ae hk (fun i => fe _ (persistent_protected c i))
  have vgood : ae.regs 15 = true ↔ SubexpPackingParameters.GoodInput n := by
    simpa only [show BinaryArithmetic.toNat (a.stacks (persistent c 4)) = SubexpPackingParameters.s n from
      hk 4 (by decide), SubexpPackingParameters.GoodInput] using ve
  by_cases hn : SubexpPackingParameters.GoodInput n
  · obtain ⟨ts, b, es, ks, vs, vb, fs⟩ := scalarSetup_eval c n ae hn ke
    refine ⟨_, b, .seq ee (.ite_true (vgood.mpr hn) es), vb, fun _ => ⟨ks, vs⟩, ?_⟩
    intro i hi
    exact (fs i hi).trans (fe _ (persistent_protected c i))
  · have hfalse : ae.regs 15 = false := by
      cases hb : ae.regs 15 with
      | false => rfl
      | true => exact False.elim (hn (vgood.mp hb))
    have hnot : ¬ DyadicSchedule.Ready c.k c.T n := fun h => hn h.1
    refine ⟨_, ae, .seq ee (.ite_false hfalse (.base (.skip ae))), ?_, ?_, ?_⟩
    · simp only [hfalse, Bool.false_eq_true, false_iff]
      exact hnot
    · intro hg
      exact False.elim (hn hg)
    · intro i _
      exact fe _ (persistent_protected c i)

/-- Every input takes a real finite path. Small-log inputs set the false guard;
valid-domain inputs compute the complete parameter and threshold data. -/
theorem command_eval (c : Config) (n : ℕ) (a : SetupState c)
    (hk : Known c n initialKnown a) :
    ∃ t b, Eval (command c) t a b ∧
      (b.regs 15 = true ↔ DyadicSchedule.Ready c.k c.T n) ∧
      (SubexpPackingParameters.GoodInput n → ScalarValues c n b ∧ ThresholdValues c n b) ∧
      RetainedFrame c a b ∧ (∀ i, i.val < helperSize c → b.stacks i = []) := by
  obtain ⟨ts, bs, es, vs, ks, fs⟩ := scalarCommand_eval c n a hk
  obtain ⟨ec, fc, hc⟩ := workspace_cleanup c bs
  let b := clearManyState (workspacePorts c) bs
  refine ⟨_, b, .seq es ec, ?_, ?_, ?_, hc⟩
  · rw [fc.1]
    exact vs
  · intro hg
    have kk := known_frame c n finalKnown bs b (ks hg).1
      (fun i => fc.2 _ (persistent_protected c i) (by simp))
    refine ⟨finalKnown_scalars c n b kk, ?_⟩
    intro i
    exact (congrArg BinaryArithmetic.toNat (fc.2 _ (threshold_protected c i) (by simp))).trans ((ks hg).2 i)
  · intro i hi
    exact (fc.2 _ (persistent_protected c i) (by simp)).trans (fs i hi)

/-- Compilation preserves the complete finite setup execution. -/
theorem program_execution (c : Config) (n : ℕ) (a : SetupState c)
    (hk : Known c n initialKnown a) :
    ∃ t b, Trace (program c) t (a.withPC (some (program c).entry)) (b.withPC none) ∧
      (b.regs 15 = true ↔ DyadicSchedule.Ready c.k c.T n) ∧
      (SubexpPackingParameters.GoodInput n → ScalarValues c n b ∧ ThresholdValues c n b) ∧
      RetainedFrame c a b ∧ (∀ i, i.val < helperSize c → b.stacks i = []) := by
  obtain ⟨t, b, he, hv, hs, hf, hw⟩ := command_eval c n a hk
  exact ⟨t + 1, b, compiled_halt_trace he (persistent c 0) (persistent c 0), hv, hs, hf, hw⟩

theorem command_zero_false (c : Config) (a : SetupState c)
    (hk : Known c 0 initialKnown a) :
    ∃ t b, Eval (command c) t a b ∧ b.regs 15 = false ∧ RetainedFrame c a b ∧
      (∀ i, i.val < helperSize c → b.stacks i = []) := by
  obtain ⟨t, b, he, hv, _, hf, hw⟩ := command_eval c 0 a hk
  refine ⟨t, b, he, ?_, hf, hw⟩
  cases hb : b.regs 15 with
  | false => rfl
  | true =>
      have hn := (hv.mp hb).1
      simp [SubexpPackingParameters.GoodInput] at hn

end SubexponentialSAT.SubexpSetupProgram

end OAI.Algorithms
