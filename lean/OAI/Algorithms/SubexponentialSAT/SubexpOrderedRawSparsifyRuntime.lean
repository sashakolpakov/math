import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpOrderedRawBoot
import OAI.Algorithms.SubexponentialSAT.ExecDyadicSparsifierRuntime

namespace OAI.Algorithms

/-!
# Runtime of the actual ordered-raw sparsification phase

The same ordered-list execution supplies the frontend words, numerical setup,
normalizer output, and threshold-bank lengths. The bound includes the
normalizer, singleton-worklist loader, concrete observed traversal, final
leaf-stream transfer, and register cleanup.
-/

namespace SubexponentialSAT.SubexpOrderedRawSparsifyRuntime

open Filter BitProgram StructuredCalls
open SubexpMainProgram SubexpSetupProgram
open ExecSparsifyWorklist (normalizedInput)
open ExecSparsifyObserved (encode)
open DyadicMaskedSearchBounds (arity)
open DyadicSparsifyNodeBounds (arity_ge_two)

variable {c : Config} {er n : ℕ} {hr : 32 ≤ workRegs er} {F : SubexpOrderedRawPrefix.Formula n}

noncomputable def localFrame (run : SubexpOrderedRawBoot.Run c hr F) : ExecSparsifyNode.Data c.k :=
  SubexpConcreteNode.localFrame c hr (SubexpOrderedRawSparsify.inputFrame c hr F run.middle)

theorem frameReady (run : SubexpOrderedRawBoot.Run c hr F) :
    ExecSparsifyBoundary.FrameReady (localFrame run) :=
  SubexpConcreteNode.local_ready c hr _ run.frameReady

theorem bankValues (run : SubexpOrderedRawBoot.Run c hr F) :
    ExecSparsifyObserved.BankValues (arity c.T n) (localFrame run) :=
  SubexpConcreteNode.local_bank c hr _ _ run.bankValues

theorem leaves_eq (run : SubexpOrderedRawBoot.Run c hr F) :
    run.leaves = ExecSparsifyObserved.leaves (localFrame run) (arity c.T n)
      (frameReady run) (bankValues run) (arity_ge_two c.k c.T n) (normalizedInput F) := rfl

/-- The raw bank-word bound is recovered from the same setup and normalizer
executions, including the selector's exact output bytes. -/
theorem bankLengths (run : SubexpOrderedRawBoot.Run c hr F)
    (hgood : SubexpPackingParameters.GoodInput n) :
    DyadicSparsifyNodeBounds.BankLengths c.k c.T n (localFrame run) := by
  have hp := SubexpOrderedRawPrefix.facts_of_execution F run.prefixTrace
  obtain ⟨tn, _, hn⟩ := run.normalization
  let G := F.map (List.map Encoding.literalCode)
  have hbody : run.afterSetup.stacks (persistent (mainExtraStacks c) 0) =
      SubexpNormalizationProgram.formulaCode G :=
    (run.setupPost.retained 0 ⟨by decide, Or.inl (by decide)⟩).trans
      (hp.body.trans (SubexpOrderedRawSparsify.body_code F).symm)
  have hi := SubexpSparsifyInput.setup_normalization_input c hr
    (SubexpConcreteNode.program c hr) hp.variableCount hp.scale hp.capacity hgood
    run.setupTrace G hbody hn (encode (normalizedInput F))
  obtain ⟨_, _, _, hrows, hword⟩ := hi
  intro i
  rw [SubexpConcreteNode.search_threshold_eq]
  have hrow := hrows i
  rw [hword] at hrow
  exact hrow

noncomputable def fullBound (run : SubexpOrderedRawBoot.Run c hr F) : ℕ :=
  SubexpOrderedRawSparsify.bound c hr F (DyadicSchedule.M c.T n)
    (DyadicSchedule.M_ge_two c.T n) run.middle run.frameReady run.bankValues

/-- Exact accounting for the implemented wrapper around the traversal. -/
theorem fullBound_eq (run : SubexpOrderedRawBoot.Run c hr F) :
    fullBound run =
      3500 * ((encode F).length + 1) ^ 2 +
      15 * (encode (normalizedInput F)).length +
      ExecEncodedSparsifier.runCost (localFrame run) (arity c.T n)
        (frameReady run) (bankValues run) (arity_ge_two c.k c.T n) (normalizedInput F) +
      6 * (Encoding.encodeList encode run.leaves).length + workRegs er + 39 := by
  let V : ℕ := ExecWorklistLoop.nodeWork encode
    (ExecSparsifyObserved.branching (localFrame run) (arity c.T n)
      (frameReady run) (bankValues run) (arity_ge_two c.k c.T n))
    (fun G => ExecSparsifyExecution.cost (localFrame run) (arity c.T n)
      (frameReady run) (bankValues run) (arity_ge_two c.k c.T n) G + 1)
    (normalizedInput F)
  change 3500 * ((encode F).length + 1) ^ 2 +
      (15 * (encode (normalizedInput F)).length + V +
        6 * (Encoding.encodeList encode run.leaves).length + workRegs er + 44) + 1 =
    3500 * ((encode F).length + 1) ^ 2 +
      15 * (encode (normalizedInput F)).length + (V + 6) +
        6 * (Encoding.encodeList encode run.leaves).length + workRegs er + 39
  omega

theorem rawBody_le_input : (encode F).length ≤ SubexpOrderedRawPrefix.bitLength F := by
  change (encode F).length ≤
    (Encoding.encodeNat n ++ SubexpOrderedRawPrefix.body F).length
  rw [List.length_append]
  change (encode F).length ≤ (Encoding.encodeNat n).length + (encode F).length
  omega

theorem normalizedBody_le_input :
    (encode (normalizedInput F)).length ≤ SubexpOrderedRawPrefix.bitLength F :=
  (SubexpOrderedRawSparsify.normalized_length_le F).trans rawBody_le_input

private theorem runtime_degree_le (A d D L n : ℕ) (hd : d ≤ D) :
    SubexpComputation.runtimeBound (A : ℝ) 3 d L n ≤
      (A : ℝ) * (((L : ℝ) + 1) ^ D * (2 : ℝ) ^ (3 * SubexpComputation.scale n)) := by
  have hb : (1 : ℝ) ≤ (L : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  have hp := pow_le_pow_right₀ hb hd
  unfold SubexpComputation.runtimeBound
  calc
    _ ≤ (A : ℝ) * ((L : ℝ) + 1) ^ D * (2 : ℝ) ^ (3 * SubexpComputation.scale n) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg A)) (by positivity)
    _ = _ := by ring

/-- Both concrete expensive terms have already been bounded. This scalar
step pays for every remaining implemented wrapper instruction. -/
private theorem phase_bound (run : SubexpOrderedRawBoot.Run c hr F)
    (A d B e : ℕ)
    (ht : ((ExecEncodedSparsifier.runCost (localFrame run) (arity c.T n)
      (frameReady run) (bankValues run) (arity_ge_two c.k c.T n) (normalizedInput F)) : ℝ) ≤
        SubexpComputation.runtimeBound (A : ℝ) 3 d (SubexpOrderedRawPrefix.bitLength F) n)
    (hl : ((Encoding.encodeList encode run.leaves).length : ℝ) ≤
      SubexpComputation.runtimeBound (B : ℝ) 2 e (SubexpOrderedRawPrefix.bitLength F) n) :
    (fullBound run : ℝ) ≤
      SubexpComputation.runtimeBound ((A + 6 * B + workRegs er + 3554 : ℕ) : ℝ)
        3 (d + e + 2) (SubexpOrderedRawPrefix.bitLength F) n := by
  let L := SubexpOrderedRawPrefix.bitLength F
  let X := ((L : ℝ) + 1) ^ (d + e + 2) * (2 : ℝ) ^ (3 * SubexpComputation.scale n)
  have hbase : (1 : ℝ) ≤ (L : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) L
    linarith
  have hexp : (1 : ℝ) ≤ (2 : ℝ) ^ (3 * SubexpComputation.scale n) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (by norm_num) (SubexpComputation.scale_nonneg n))
  have hX : 1 ≤ X := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hbase) hexp
  have hsq : ((L : ℝ) + 1) ^ 2 ≤ X := by
    calc
      _ ≤ ((L : ℝ) + 1) ^ (d + e + 2) := pow_le_pow_right₀ hbase (by omega)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hexp
  have hraw : ((encode F).length : ℝ) ≤ L := by
    exact_mod_cast (rawBody_le_input (F := F))
  have hnorm : ((encode (normalizedInput F)).length : ℝ) ≤ L := by
    exact_mod_cast (normalizedBody_le_input (F := F))
  have hrawCost : (3500 : ℝ) * (((encode F).length : ℝ) + 1) ^ 2 ≤ 3500 * X := by
    exact mul_le_mul_of_nonneg_left
      ((pow_le_pow_left₀ (by positivity) (by linarith :
        ((encode F).length : ℝ) + 1 ≤ (L : ℝ) + 1) 2).trans hsq)
      (by norm_num)
  have hnormX : ((encode (normalizedInput F)).length : ℝ) ≤ X := by
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith
  have ht' : ((ExecEncodedSparsifier.runCost (localFrame run) (arity c.T n)
      (frameReady run) (bankValues run) (arity_ge_two c.k c.T n) (normalizedInput F)) : ℝ) ≤
      (A : ℝ) * X := ht.trans (runtime_degree_le A d (d + e + 2) L n (by omega))
  have hl' : ((Encoding.encodeList encode run.leaves).length : ℝ) ≤ (B : ℝ) * X :=
    (hl.trans (SubexpComputation.runtimeBound_mono_exponent (Nat.cast_nonneg B)
      (by norm_num : (2 : ℝ) ≤ 3) e L n)).trans
      (runtime_degree_le B e (d + e + 2) L n (by omega))
  have hwX : (workRegs er : ℝ) + 39 ≤ ((workRegs er : ℝ) + 39) * X :=
    le_mul_of_one_le_right (by positivity) hX
  have hfull : (fullBound run : ℝ) ≤ ((A + 6 * B + workRegs er + 3554 : ℕ) : ℝ) * X := by
    rw [fullBound_eq]
    push_cast
    nlinarith
  calc
    _ ≤ ((A + 6 * B + workRegs er + 3554 : ℕ) : ℝ) * X := hfull
    _ = _ := by dsimp [X, SubexpComputation.runtimeBound]; ring

/-- Full actual main-phase bound, with no word-size or node-runtime premise
left: those follow from the retained executions in `Run`. -/
theorem fullBound_bound (c : Config) {er : ℕ} (hr : 32 ≤ workRegs er) :
    ∃ A d : ℕ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, ∀ (F : SubexpOrderedRawPrefix.Formula n),
      ExecSunflowerSearch.RawWidthAtMost c.k F → ∀ run : SubexpOrderedRawBoot.Run c hr F,
        (fullBound run : ℝ) ≤ SubexpComputation.runtimeBound (A : ℝ) 3 d
          (SubexpOrderedRawPrefix.bitLength F) n := by
  obtain ⟨A, d, _, ht⟩ := ExecDyadicSparsifierRuntime.runCost_bound c.k c.T c.width_ge_two c.control
  obtain ⟨B, e, _, hl⟩ := ExecDyadicSparsifierRuntime.encoded_leaves_bound
    c.k c.T c.width_ge_two c.control
  refine ⟨A + 6 * B + workRegs er + 3554, d + e + 2, by omega, ?_⟩
  filter_upwards [ht, SubexpPackingParameters.eventually_goodInput] with n ht hgood
  intro F hF run
  have hready := ExecSparsifyStartup.normalizedInput_ready F c.k hF
  have hanti := ExecSparsifyStartup.normalizedInput_antichain F
  have hnL := SubexpOrderedRawPrefix.numVariables_le_bitLength F
  have htime := ht (SubexpOrderedRawPrefix.bitLength F) (localFrame run) (frameReady run)
    (bankValues run) (bankLengths run hgood) (normalizedInput F) hready hanti hnL
  have hleaf := hl n hgood (SubexpOrderedRawPrefix.bitLength F) (localFrame run) (frameReady run)
    (bankValues run) (normalizedInput F) hready hanti hnL
  rw [← leaves_eq run] at hleaf
  exact phase_bound run A d B e htime hleaf

theorem sparsifySteps_bound (c : Config) {er : ℕ} (hr : 32 ≤ workRegs er) :
    ∃ A d : ℕ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, ∀ (F : SubexpOrderedRawPrefix.Formula n),
      ExecSunflowerSearch.RawWidthAtMost c.k F → ∀ run : SubexpOrderedRawBoot.Run c hr F,
        (run.sparsifySteps : ℝ) ≤ SubexpComputation.runtimeBound (A : ℝ) 3 d
          (SubexpOrderedRawPrefix.bitLength F) n := by
  obtain ⟨A, d, hA, hb⟩ := fullBound_bound c hr
  refine ⟨A, d, hA, hb.mono ?_⟩
  intro n hn F hF run
  exact (Nat.cast_le.mpr run.sparsifyBound).trans (hn F hF run)

/-- The main phase exposes the very same bounded leaf list used by the
downstream leaf iterator. -/
theorem leaves_bound (c : Config) {er : ℕ} (hr : 32 ≤ workRegs er) :
    ∃ A d : ℕ, 0 < A ∧ ∀ n : ℕ, SubexpPackingParameters.GoodInput n →
      ∀ (F : SubexpOrderedRawPrefix.Formula n), ExecSunflowerSearch.RawWidthAtMost c.k F →
      ∀ run : SubexpOrderedRawBoot.Run c hr F,
        (run.leaves.length : ℝ) ≤ SubexpComputation.runtimeBound (A : ℝ) 2 d
          (SubexpOrderedRawPrefix.bitLength F) n := by
  obtain ⟨A, d, hA, hl⟩ := ExecDyadicSparsifierRuntime.leaves_bound
    c.k c.T c.width_ge_two c.control
  refine ⟨A, d, hA, ?_⟩
  intro n hgood F hF run
  rw [leaves_eq run]
  exact hl n hgood (SubexpOrderedRawPrefix.bitLength F) (localFrame run) (frameReady run)
    (bankValues run) (normalizedInput F)
    (ExecSparsifyStartup.normalizedInput_ready F c.k hF)
    (ExecSparsifyStartup.normalizedInput_antichain F)
    (SubexpOrderedRawPrefix.numVariables_le_bitLength F)

end SubexponentialSAT.SubexpOrderedRawSparsifyRuntime


end OAI.Algorithms
