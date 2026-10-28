import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainBoot
import OAI.Algorithms.SubexponentialSAT.ExecDyadicSparsifierRuntime

namespace OAI.Algorithms

/-!
# Runtime of the actual main sparsification phase

The same raw-input execution supplies the frontend words, numerical setup,
normalizer output, and threshold-bank lengths. The bound includes the
normalizer, singleton-worklist loader, concrete observed traversal, final
leaf-stream transfer, and register cleanup.
-/

namespace SubexponentialSAT.SubexpActualSparsifyRuntime

open Filter BitProgram StructuredCalls
open SubexpMainProgram SubexpSetupProgram
open SubexpNormalizationCorrectness (normalizedFormula)
open ExecSparsifyObserved (encode)
open DyadicMaskedSearchBounds (arity)
open DyadicSparsifyNodeBounds (arity_ge_two)

variable {c : Config} {er n : ℕ} {hr : 32 ≤ workRegs er} {F : SAT.CNF (Fin n)}

noncomputable def localFrame (run : SubexpMainBoot.Run c hr F) : ExecSparsifyNode.Data c.k :=
  SubexpConcreteNode.localFrame c hr (SubexpActualSparsify.inputFrame c hr F run.middle)

theorem frameReady (run : SubexpMainBoot.Run c hr F) :
    ExecSparsifyBoundary.FrameReady (localFrame run) :=
  SubexpConcreteNode.local_ready c hr _ run.frameReady

theorem bankValues (run : SubexpMainBoot.Run c hr F) :
    ExecSparsifyObserved.BankValues (arity c.T n) (localFrame run) :=
  SubexpConcreteNode.local_bank c hr _ _ run.bankValues

theorem leaves_eq (run : SubexpMainBoot.Run c hr F) :
    run.leaves = ExecSparsifyObserved.leaves (localFrame run) (arity c.T n)
      (frameReady run) (bankValues run) (arity_ge_two c.k c.T n) (normalizedFormula F) := rfl

/-- The raw bank-word bound is recovered from the same setup and normalizer
executions, including the selector's exact output bytes. -/
theorem bankLengths (run : SubexpMainBoot.Run c hr F)
    (hgood : SubexpPackingParameters.GoodInput n) :
    DyadicSparsifyNodeBounds.BankLengths c.k c.T n (localFrame run) := by
  have hp := SubexpMainBootPrefix.facts_of_execution F run.prefixTrace
  obtain ⟨tn, _, hn⟩ := run.normalization
  let G := (ExecQuantitativeSparsify.formulaList F).map (List.map Encoding.literalCode)
  have hbody : run.afterSetup.stacks (persistent (mainExtraStacks c) 0) =
      SubexpNormalizationProgram.formulaCode G :=
    (run.setupPost.retained 0 ⟨by decide, Or.inl (by decide)⟩).trans
      (hp.body.trans (SubexpNormalizationCorrectness.canonical_body_eq F).symm)
  have hi := SubexpSparsifyInput.setup_normalization_input c hr
    (SubexpConcreteNode.program c hr) hp.variableCount hp.scale hp.capacity hgood
    run.setupTrace G hbody hn (encode (normalizedFormula F))
  obtain ⟨_, _, _, hrows, hword⟩ := hi
  intro i
  rw [SubexpConcreteNode.search_threshold_eq]
  have hrow := hrows i
  rw [hword] at hrow
  exact hrow

noncomputable def fullBound (run : SubexpMainBoot.Run c hr F) : ℕ :=
  SubexpActualSparsify.bound c hr F (DyadicSchedule.M c.T n)
    (DyadicSchedule.M_ge_two c.T n) run.middle run.frameReady run.bankValues

/-- Exact accounting for the implemented wrapper around the traversal. -/
theorem fullBound_eq (run : SubexpMainBoot.Run c hr F) :
    fullBound run =
      3500 * ((Encoding.encodeCNFBody F).length + 1) ^ 2 +
      15 * (encode (normalizedFormula F)).length +
      ExecEncodedSparsifier.runCost (localFrame run) (arity c.T n)
        (frameReady run) (bankValues run) (arity_ge_two c.k c.T n) (normalizedFormula F) +
      6 * (Encoding.encodeList encode run.leaves).length + workRegs er + 39 := by
  let V : ℕ := ExecWorklistLoop.nodeWork encode
    (ExecSparsifyObserved.branching (localFrame run) (arity c.T n)
      (frameReady run) (bankValues run) (arity_ge_two c.k c.T n))
    (fun G => ExecSparsifyExecution.cost (localFrame run) (arity c.T n)
      (frameReady run) (bankValues run) (arity_ge_two c.k c.T n) G + 1)
    (normalizedFormula F)
  change 3500 * ((Encoding.encodeCNFBody F).length + 1) ^ 2 +
      (15 * (encode (normalizedFormula F)).length + V +
        6 * (Encoding.encodeList encode run.leaves).length + workRegs er + 44) + 1 =
    3500 * ((Encoding.encodeCNFBody F).length + 1) ^ 2 +
      15 * (encode (normalizedFormula F)).length + (V + 6) +
        6 * (Encoding.encodeList encode run.leaves).length + workRegs er + 39
  omega

theorem rawBody_le_input : (Encoding.encodeCNFBody F).length ≤ Encoding.formulaBitLength F := by
  rw [Encoding.formulaBitLength_eq]
  omega

theorem normalizedBody_le_input :
    (encode (normalizedFormula F)).length ≤ Encoding.formulaBitLength F :=
  (ExecSparsifyStartup.normalizedFormula_body_length_le F).trans rawBody_le_input

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
private theorem phase_bound (run : SubexpMainBoot.Run c hr F)
    (A d B e : ℕ)
    (ht : ((ExecEncodedSparsifier.runCost (localFrame run) (arity c.T n)
      (frameReady run) (bankValues run) (arity_ge_two c.k c.T n) (normalizedFormula F)) : ℝ) ≤
        SubexpComputation.runtimeBound (A : ℝ) 3 d (Encoding.formulaBitLength F) n)
    (hl : ((Encoding.encodeList encode run.leaves).length : ℝ) ≤
      SubexpComputation.runtimeBound (B : ℝ) 2 e (Encoding.formulaBitLength F) n) :
    (fullBound run : ℝ) ≤
      SubexpComputation.runtimeBound ((A + 6 * B + workRegs er + 3554 : ℕ) : ℝ)
        3 (d + e + 2) (Encoding.formulaBitLength F) n := by
  let L := Encoding.formulaBitLength F
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
  have hraw : ((Encoding.encodeCNFBody F).length : ℝ) ≤ L := by
    exact_mod_cast (rawBody_le_input (F := F))
  have hnorm : ((encode (normalizedFormula F)).length : ℝ) ≤ L := by
    exact_mod_cast (normalizedBody_le_input (F := F))
  have hrawCost : (3500 : ℝ) * (((Encoding.encodeCNFBody F).length : ℝ) + 1) ^ 2 ≤ 3500 * X := by
    exact mul_le_mul_of_nonneg_left
      ((pow_le_pow_left₀ (by positivity) (by linarith :
        ((Encoding.encodeCNFBody F).length : ℝ) + 1 ≤ (L : ℝ) + 1) 2).trans hsq)
      (by norm_num)
  have hnormX : ((encode (normalizedFormula F)).length : ℝ) ≤ X := by
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith
  have ht' : ((ExecEncodedSparsifier.runCost (localFrame run) (arity c.T n)
      (frameReady run) (bankValues run) (arity_ge_two c.k c.T n) (normalizedFormula F)) : ℝ) ≤
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
    ∃ A d : ℕ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, ∀ (F : SAT.CNF (Fin n)),
      SAT.WidthAtMost c.k F → ∀ run : SubexpMainBoot.Run c hr F,
        (fullBound run : ℝ) ≤ SubexpComputation.runtimeBound (A : ℝ) 3 d
          (Encoding.formulaBitLength F) n := by
  obtain ⟨A, d, _, ht⟩ := ExecDyadicSparsifierRuntime.runCost_bound c.k c.T c.width_ge_two c.control
  obtain ⟨B, e, _, hl⟩ := ExecDyadicSparsifierRuntime.encoded_leaves_bound
    c.k c.T c.width_ge_two c.control
  refine ⟨A + 6 * B + workRegs er + 3554, d + e + 2, by omega, ?_⟩
  filter_upwards [ht, SubexpPackingParameters.eventually_goodInput] with n ht hgood
  intro F hF run
  have hready := ExecSparsifyStartup.normalizedFormula_ready F c.k hF
  have hanti := ExecSparsifyStartup.normalizedFormula_antichain F
  have hnL := Encoding.numVariables_le_formulaBitLength F
  have htime := ht (Encoding.formulaBitLength F) (localFrame run) (frameReady run)
    (bankValues run) (bankLengths run hgood) (normalizedFormula F) hready hanti hnL
  have hleaf := hl n hgood (Encoding.formulaBitLength F) (localFrame run) (frameReady run)
    (bankValues run) (normalizedFormula F) hready hanti hnL
  rw [← leaves_eq run] at hleaf
  exact phase_bound run A d B e htime hleaf

theorem sparsifySteps_bound (c : Config) {er : ℕ} (hr : 32 ≤ workRegs er) :
    ∃ A d : ℕ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, ∀ (F : SAT.CNF (Fin n)),
      SAT.WidthAtMost c.k F → ∀ run : SubexpMainBoot.Run c hr F,
        (run.sparsifySteps : ℝ) ≤ SubexpComputation.runtimeBound (A : ℝ) 3 d
          (Encoding.formulaBitLength F) n := by
  obtain ⟨A, d, hA, hb⟩ := fullBound_bound c hr
  refine ⟨A, d, hA, hb.mono ?_⟩
  intro n hn F hF run
  exact (Nat.cast_le.mpr run.sparsifyBound).trans (hn F hF run)

/-- The main phase exposes the very same bounded leaf list used by the
downstream leaf iterator. -/
theorem leaves_bound (c : Config) {er : ℕ} (hr : 32 ≤ workRegs er) :
    ∃ A d : ℕ, 0 < A ∧ ∀ n : ℕ, SubexpPackingParameters.GoodInput n →
      ∀ (F : SAT.CNF (Fin n)), SAT.WidthAtMost c.k F →
      ∀ run : SubexpMainBoot.Run c hr F,
        (run.leaves.length : ℝ) ≤ SubexpComputation.runtimeBound (A : ℝ) 2 d
          (Encoding.formulaBitLength F) n := by
  obtain ⟨A, d, hA, hl⟩ := ExecDyadicSparsifierRuntime.leaves_bound
    c.k c.T c.width_ge_two c.control
  refine ⟨A, d, hA, ?_⟩
  intro n hgood F hF run
  rw [leaves_eq run]
  exact hl n hgood (Encoding.formulaBitLength F) (localFrame run) (frameReady run)
    (bankValues run) (normalizedFormula F)
    (ExecSparsifyStartup.normalizedFormula_ready F c.k hF)
    (ExecSparsifyStartup.normalizedFormula_antichain F)
    (Encoding.numVariables_le_formulaBitLength F)

end SubexponentialSAT.SubexpActualSparsifyRuntime

end OAI.Algorithms
