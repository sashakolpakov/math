import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStages

namespace OAI.Algorithms

/-! The actual early and final branches of the closed numerical setup. -/

namespace SubexponentialSAT.SubexpSetupProgram

open BitProgram StructuredCalls SubexpSetupStorage

theorem early_eval (c : Config) (a : SetupState c) :
    ∃ t b, Eval (early c) t a b ∧
      (b.regs 15 = true ↔ 32 ≤ BinaryArithmetic.toNat (a.stacks (persistent c 4))) ∧
      (∀ i, Protected c i → b.stacks i = a.stacks i) := by
  let hs : 6 < helperSize c := small_fits c (by decide)
  let inputs : List (Fin (stackCount c) × Fin 6) := [(persistent c 4, 0)]
  let start := project guardRegister (workPort c hs) (prepared c hs inputs a)
  have hi : ∀ p ∈ inputs, Protected c p.1 := by
    intro p hp
    simp only [inputs, List.mem_singleton] at hp
    subst p
    exact persistent_protected c 4
  have hv : start.stacks 0 = a.stacks (persistent c 4) :=
    prepared_word c hs inputs a hi (by simp [inputs]) (persistent c 4, 0) (by simp [inputs])
  have hz : start.stacks 1 = [] := by
    apply prepared_empty c hs inputs a 1
    intro p hp
    simp only [inputs, List.mem_singleton] at hp
    subst p
    change (1 : Fin 6) ≠ 0
    decide
  obtain ⟨out, ht, hbit, _⟩ := SubexpGuardProgram.earlyGuard_eval start hz
  let b := returned c guardRegister hs inputs [] a out
  refine ⟨stageCost c guardRegister hs inputs [] a out
    (SubexpGuardProgram.earlyGuardCost start + 1), b, ?_, ?_, ?_⟩
  · exact stage_eval c (compiled SubexpGuardProgram.earlyGuard 0 1) guardRegister
      guardRegister_injective hs inputs [] a start out hi (by simp) rfl
      (compiled_halt_trace ht 0 1)
  · rw [returned_guard_flag]
    simpa only [hv] using hbit
  · intro i hi'
    exact returned_frame c guardRegister hs inputs [] a out i hi' (by simp)

/-- The six actual encoded operands yield the exact three-part guard. -/
theorem readyGuard_eval (c : Config) (n : ℕ) (a : SetupState c)
    (hsval : BinaryArithmetic.toNat (a.stacks (persistent c 4)) = SubexpPackingParameters.s n)
    (hcval : BinaryArithmetic.toNat (a.stacks (persistent c 28)) = 32)
    (hdval : BinaryArithmetic.toNat (a.stacks (persistent c 19)) = SubexpPackingParameters.D n)
    (hstval : BinaryArithmetic.toNat (a.stacks (persistent c 20)) = DyadicSchedule.Dstar c.k c.T n)
    (hsqval : BinaryArithmetic.toNat (a.stacks (persistent c 26)) = DyadicSchedule.R c.k c.T n ^ 2)
    (htval : BinaryArithmetic.toNat (a.stacks (persistent c 27)) =
      16 * DyadicSchedule.Q n * DyadicSchedule.delta c.k c.T n * SubexpPackingParameters.s n) :
    ∃ t b, Eval (readyGuard c) t a b ∧
      (b.regs 15 = true ↔ DyadicSchedule.Ready c.k c.T n) ∧
      (∀ i, Protected c i → b.stacks i = a.stacks i) := by
  let hs : 6 < helperSize c := small_fits c (by decide)
  let inputs : List (Fin (stackCount c) × Fin 6) :=
    [(persistent c 4, 0), (persistent c 28, 1), (persistent c 26, 2),
      (persistent c 27, 3), (persistent c 19, 4), (persistent c 20, 5)]
  let start := project guardRegister (workPort c hs) (prepared c hs inputs a)
  have hi : ∀ p ∈ inputs, Protected c p.1 := by
    intro p hp
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact persistent_protected c _
  have hd : (inputs.map Prod.snd).Nodup := by simp [inputs]
  have hv (p : Fin (stackCount c) × Fin 6) (hp : p ∈ inputs) :
      start.stacks p.2 = a.stacks p.1 := prepared_word c hs inputs a hi hd p hp
  have h0 := hv (persistent c 4, 0) (by simp [inputs])
  have h1 := hv (persistent c 28, 1) (by simp [inputs])
  have h2 := hv (persistent c 26, 2) (by simp [inputs])
  have h3 := hv (persistent c 27, 3) (by simp [inputs])
  have h4 := hv (persistent c 19, 4) (by simp [inputs])
  have h5 := hv (persistent c 20, 5) (by simp [inputs])
  have hpass : SubexpGuardProgram.guardPass start = true ↔ DyadicSchedule.Ready c.k c.T n := by
    simp only [SubexpGuardProgram.guardPass, Bool.and_eq_true,
      SubexpGuardProgram.pairPass, SubexpGuardProgram.pairStack]
    norm_num
    rw [h0, h1, h2, h3, h4, h5, hsval, hcval, hdval, hstval, hsqval, htval]
    change (_ ∧ _) ∧ _ ↔ _ ∧ _ ∧ _
    exact and_assoc
  obtain ⟨out, ht, hbit⟩ := SubexpGuardProgram.guard_eval start
  let b := returned c guardRegister hs inputs [] a out
  refine ⟨stageCost c guardRegister hs inputs [] a out (SubexpGuardProgram.guardCost start + 1),
    b, ?_, ?_, ?_⟩
  · exact stage_eval c (compiled SubexpGuardProgram.guard 0 1) guardRegister
      guardRegister_injective hs inputs [] a start out hi (by simp) rfl
      (compiled_halt_trace ht 0 1)
  · rw [returned_guard_flag, hbit]
    exact hpass
  · intro i hi'
    exact returned_frame c guardRegister hs inputs [] a out i hi' (by simp)

theorem cutoff_eval (c : Config) (a : SetupState c) :
    ∃ t b, Eval (cutoff c) t a b ∧
      BinaryArithmetic.toNat (b.stacks (persistent c 28)) = 32 ∧
      Preserves c [persistent c 28] a b := by
  let mid := clearManyState [persistent c 28] a
  let b := SubexpGuardProgram.loadThirtyTwoState (0 : Fin 16) (persistent c 28) mid
  refine ⟨clearManyCost [persistent c 28] a + 8, b,
    .seq (clearMany_eval _ a) (.base (SubexpGuardProgram.loadThirtyTwo_eval _ _ mid)), ?_, ?_⟩
  · exact SubexpGuardProgram.loadThirtyTwo_value _ _ mid (by simp [mid, clearMany_stacks])
  · constructor
    · change (Function.update mid.regs 0 false) 15 = a.regs 15
      rw [Function.update_of_ne (by decide)]
      exact clearMany_reg_frame _ _ _ (by decide) (by decide)
    · intro i hi hm
      have hne : i ≠ persistent c 28 := by simpa using hm
      exact (SubexpGuardProgram.loadThirtyTwo_frame _ _ mid i hne).trans (by
        simp [mid, clearMany_stacks, hne])

theorem colors_eval (c : Config) (a : SetupState c) :
    ∃ t b, Eval (colors c) t a b ∧
      b.stacks (persistent c 21) = a.stacks (persistent c 4) ∧
      Preserves c [persistent c 21] a b := by
  let ps := [temporary c, persistent c 21]
  let mid := clearManyState ps a
  let b := copyState (persistent c 4) (persistent c 21) mid
  have hne : persistent c 4 ≠ persistent c 21 := by
    intro he
    have hv := congrArg (fun x : Fin (stackCount c) => x.val) he
    change helperSize c + thresholdCount c + 4 = helperSize c + thresholdCount c + 21 at hv
    omega
  have htmp4 := protected_ne_temporary c (persistent_protected c 4)
  have htmp21 := protected_ne_temporary c (persistent_protected c 21)
  have ht : mid.stacks (temporary c) = [] := by simp [mid, ps, clearMany_stacks]
  refine ⟨clearManyCost ps a + (7 * (mid.stacks (persistent c 4)).length + 5 + 0), b,
    .seq (clearMany_eval ps a) (.seq (copy_eval _ _ _ mid hne htmp4 htmp21.symm ht)
      (.base (.skip b))), ?_, ?_⟩
  · simp [b, copyState, StackRoutines.copyStacks, mid, ps, clearMany_stacks, htmp4, hne]
  · constructor
    · exact (StackRoutines.readRegs_frame mid.regs 0 1 15 none (by decide) (by decide)).trans
        (clearMany_reg_frame ps a 15 (by decide) (by decide))
    · intro i hi hm
      have hni : i ≠ persistent c 21 := by simpa using hm
      have hnt := protected_ne_temporary c hi
      exact (copyState_frame _ _ _ mid hni).trans (by simp [mid, ps, clearMany_stacks, hni, hnt])

theorem workspace_cleanup (c : Config) (a : SetupState c) :
    let b := clearManyState (workspacePorts c) a
    Eval (clearMany (workspacePorts c)) (clearManyCost (workspacePorts c) a) a b ∧
      Preserves c [] a b ∧
      (∀ i, i.val < helperSize c → b.stacks i = []) := by
  dsimp only
  refine ⟨clearMany_eval _ a, ⟨clearMany_reg_frame _ _ _ (by decide) (by decide), ?_⟩, ?_⟩
  · intro i hi _
    rw [clearMany_stacks]
    apply ite_eq_right
    simp only [workspacePorts, List.mem_ofFn, not_exists]
    intro j hj
    have hv := congrArg Fin.val hj
    have := j.isLt
    unfold Protected at hi
    simp only at hv
    omega
  · intro i hi
    rw [clearMany_stacks]
    apply ite_eq_left
    simp only [workspacePorts, List.mem_ofFn]
    exact ⟨⟨i.val, hi⟩, Fin.ext rfl⟩

end SubexponentialSAT.SubexpSetupProgram

end OAI.Algorithms
