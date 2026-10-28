import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupParameterBound
import OAI.Algorithms.SubexponentialSAT.SubexpSetupArithmeticBounds
import OAI.Algorithms.SubexponentialSAT.SubexpSetupBlockBounds
import OAI.Algorithms.SubexponentialSAT.SubexpSetupControlBounds
import OAI.Algorithms.SubexponentialSAT.SubexpSetupPhaseTableCost
import OAI.Algorithms.SubexponentialSAT.SubexpSetupExecution

namespace OAI.Algorithms

/-!
# Polynomial runtime for the actual numerical setup

The proof composes the named instruction tables and their measured local
bounds. Runtime parameters are bounded using the implemented dyadic schedule.
The constants in `PolynomialRun` are fixed before input sizes and states.
-/

namespace SubexponentialSAT.SubexpSetupRuntime

open BitProgram StructuredCalls SubexpSetupStorage SubexpSetupProgram
open SubexpSetupBoundSpec SubexpSetupParameterBound SubexpSetupPhaseArithmetic
open Filter

private theorem extend_one (c : Config) (n : ℕ) (old : List (Fin 32))
    (i : Fin 32) (a b : SetupState c) (hk : Known c n old a)
    (hf : Preserves c [persistent c i] a b)
    (hv : wordValue c b i = wanted c n i) : Known c n (old ++ [i]) b := by
  apply known_extend c n old [i] a b hk
    (preserves_scalarFrame c [i] a b hf)
  intro j hj
  obtain rfl := List.mem_singleton.mp hj
  exact hv

private theorem extend_two (c : Config) (n : ℕ) (old : List (Fin 32))
    (i j : Fin 32) (a b : SetupState c) (hk : Known c n old a)
    (hf : Preserves c [persistent c i, persistent c j] a b)
    (hi : wordValue c b i = wanted c n i)
    (hj : wordValue c b j = wanted c n j) : Known c n (old ++ [i,j]) b := by
  apply known_extend c n old [i,j] a b hk
    (preserves_scalarFrame c [i,j] a b hf)
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact hi
  · obtain rfl := List.mem_singleton.mp hq
    exact hj

private theorem of_unconditional_envelope (c : Config) (cmd : SetupCmd c)
    (pre post : ℕ → SetupState c → Prop)
    (hsem : ∀ᶠ n : ℕ in atTop, ∀ a, pre n a →
      ∃ t b, Eval cmd t a b ∧ post n b)
    (hbound : ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ B P a t b,
      WordBound B a → Eval cmd t a b →
      t ≤ C * (B + P + 1) ^ q ∧ WordBound (C * (B + P + 1) ^ q) b) :
    PolynomialRun cmd pre post := by
  apply PolynomialRun.of_envelope (parameterBudget_polynomial c) hsem
  obtain ⟨C, q, hC, hq, hb⟩ := hbound
  refine ⟨C, q, hC, hq, Filter.Eventually.of_forall ?_⟩
  intro n B a t b hw _ he
  exact hb B (parameterBudget c n) a t b hw he

theorem selectM_polynomial (c : Config) (old : List (Fin 32)) (h4 : 4 ∈ old) :
    PolynomialRun (selectM c) (fun n a => Known c n old a)
      (fun n b => Known c n (old ++ [23]) b) := by
  apply of_unconditional_envelope c (selectM c) _ _ _
    (SubexpSetupArithmeticBounds.selectM_polynomial c)
  apply Filter.Eventually.of_forall
  intro n a hk
  obtain ⟨t, _, he, hv, _, hf⟩ := selectM_schedule c n a (hk 4 h4)
  exact ⟨t, selectResult c a, he, extend_one c n old 23 a _ hk hf hv⟩

theorem occurrence_polynomial (c : Config) (old : List (Fin 32)) (h23 : 23 ∈ old) :
    PolynomialRun (occurrence c) (fun n a => Known c n old a)
      (fun n b => Known c n (old ++ [24]) b) := by
  apply of_unconditional_envelope c (occurrence c) _ _ _
    (SubexpSetupArithmeticBounds.occurrence_polynomial c)
  apply Filter.Eventually.of_forall
  intro n a hk
  obtain ⟨t, rf, w, _, he, hv, _, hf⟩ := occurrence_schedule c n a (hk 23 h23)
  exact ⟨t, occurrenceResult c a rf w, he, extend_one c n old 24 a _ hk hf hv⟩

theorem incidence_polynomial (c : Config) (old : List (Fin 32))
    (h5 : 5 ∈ old) (h24 : 24 ∈ old) :
    PolynomialRun (incidence c) (fun n a => Known c n old a)
      (fun n b => Known c n (old ++ [16]) b) := by
  apply of_unconditional_envelope c (incidence c) _ _ _
    (SubexpSetupArithmeticBounds.incidence_polynomial c)
  apply Filter.Eventually.of_forall
  intro n a hk
  obtain ⟨t, rf, w, _, he, hv, _, hf⟩ := incidence_schedule c n a (hk 5 h5) (hk 24 h24)
  exact ⟨t, incidenceResult c a rf w, he, extend_one c n old 16 a _ hk hf hv⟩

theorem prime_polynomial (c : Config) (old : List (Fin 32)) (h5 : 5 ∈ old) :
    PolynomialRun (prime c) (fun n a => Known c n old a)
      (fun n b => Known c n (old ++ [6]) b) := by
  apply PolynomialRun.of_envelope (parameterBudget_polynomial c)
  · apply Filter.Eventually.of_forall
    intro n a hk
    obtain ⟨t, out, _, he, hv, _, hf⟩ := prime_schedule c n a (hk 5 h5)
    exact ⟨t, primeResult c a out, he, extend_one c n old 6 a _ hk hf hv⟩
  · obtain ⟨C, q, hC, hq, hb⟩ := SubexpSetupArithmeticBounds.prime_polynomial c
    refine ⟨C, q, hC, hq, ?_⟩
    filter_upwards [SubexpPackingParameters.eventually_goodInput] with n hn
    intro B a t b hw hk he
    apply hb B (parameterBudget c n) a t b hw _ he
    have hu : BinaryArithmetic.toNat (a.stacks (persistent c 5)) =
        SubexpPackingParameters.u n := hk 5 h5
    rw [hu]
    exact prime_scale_le c n hn

theorem field_polynomial (c : Config) (old : List (Fin 32))
    (h6 : 6 ∈ old) (h16 : 16 ∈ old) :
    PolynomialRun (field c) (fun n a => Known c n old a)
      (fun n b => Known c n (old ++ [17,25]) b) := by
  apply PolynomialRun.of_envelope (parameterBudget_polynomial c)
  · apply Filter.Eventually.of_forall
    intro n a hk
    obtain ⟨t, out, _, he, hQ, hR, _, _, _, hf⟩ := field_schedule c n a (hk 6 h6) (hk 16 h16)
    exact ⟨t, fieldResult c a out, he, extend_two c n old 17 25 a _ hk hf hQ hR⟩
  · obtain ⟨C, q, hC, hq, hb⟩ := SubexpSetupArithmeticBounds.field_polynomial c
    refine ⟨C, q, hC, hq, Filter.Eventually.of_forall ?_⟩
    intro n B a t b hw hk he
    have hp : BinaryArithmetic.toNat (a.stacks (persistent c 6)) =
        SubexpPackingParameters.p n := hk 6 h6
    have hd : BinaryArithmetic.toNat (a.stacks (persistent c 16)) =
        DyadicSchedule.delta c.k c.T n := hk 16 h16
    apply hb B (parameterBudget c n) a t b hw _ _ he
    · rw [hp]
      have := SubexpPackingParameters.p_gt_two n
      omega
    · rw [hd]
      exact DyadicSchedule.delta_pos c.k c.T n

theorem dimension_polynomial (c : Config) (old : List (Fin 32))
    (h2 : 2 ∈ old) (h5 : 5 ∈ old) :
    PolynomialRun (dimension c) (fun n a => Known c n old a)
      (fun n b => Known c n (old ++ [19]) b) := by
  apply PolynomialRun.of_envelope (parameterBudget_polynomial c)
  · filter_upwards [SubexpPackingParameters.eventually_goodInput] with n hn
    intro a hk
    obtain ⟨t, out, _, he, hv, _, hf, _⟩ :=
      SubexpSetupPhaseBlock.dimension_scheduled_eval c n a hn (hk 5 h5) (hk 2 h2)
    refine ⟨_, SubexpSetupPhaseBlock.dimensionResult c a out, he, ?_⟩
    apply known_extend c n old [19] a _ hk
    · intro i hi
      exact hf i (by simpa only [List.mem_singleton] using hi)
    · intro i hi
      obtain rfl := List.mem_singleton.mp hi
      exact hv
  · obtain ⟨C, q, hC, hq, hb⟩ := SubexpSetupBlockBounds.dimension_envelope c
    refine ⟨C, q, hC, hq, ?_⟩
    filter_upwards [SubexpPackingParameters.eventually_goodInput] with n hn
    intro B a t b hw hk he
    apply hb B (parameterBudget c n) a t b hw _ he
    have hu : BinaryArithmetic.toNat (a.stacks (persistent c 5)) =
        SubexpPackingParameters.u n := hk 5 h5
    rw [hu]
    exact SubexpPackingParameters.ell_pos hn

theorem block_polynomial (c : Config) (old : List (Fin 32))
    (h16 : 16 ∈ old) (h17 : 17 ∈ old) :
    PolynomialRun (block c) (fun n a => Known c n old a) (fun _ _ => True) := by
  apply PolynomialRun.of_envelope (parameterBudget_polynomial c)
  · apply Filter.Eventually.of_forall
    intro n a _
    obtain ⟨t, rf, w, _, _, he⟩ := SubexpSetupPhaseBlock.block_eval c a
    exact ⟨_, _, he, trivial⟩
  · obtain ⟨C, q, hC, hq, hb⟩ := SubexpSetupBlockBounds.block_envelope c
    refine ⟨C, q, hC, hq, Filter.Eventually.of_forall ?_⟩
    intro n B a t b hw hk he
    apply hb B (parameterBudget c n) a t b hw _ he
    have hd : BinaryArithmetic.toNat (a.stacks (persistent c 16)) =
        DyadicSchedule.delta c.k c.T n := hk 16 h16
    have hQ : BinaryArithmetic.toNat (a.stacks (persistent c 17)) =
        DyadicSchedule.Q n := hk 17 h17
    simpa only [SubexpBlockParameterProgram.exponentValue, hd, hQ] using
      block_exponent_le c n

theorem tail_polynomial (c : Config) :
    PolynomialRun (tailOperands c) (fun _ _ => True) (fun _ _ => True) := by
  apply of_unconditional_envelope c (tailOperands c) _ _ _
    (SubexpSetupBlockBounds.tail_envelope c)
  apply Filter.Eventually.of_forall
  intro n a _
  obtain ⟨t, rf, square, tail, _, he, _⟩ := SubexpSetupPhaseTail.eval c a
  exact ⟨_, _, he, trivial⟩

/-- The numerical prefix through the largest arithmetic block already has a
fixed polynomial bound. No schedule value is needed for later size accounting. -/
theorem throughBlock_polynomial (c : Config) :
    PolynomialRun
      (.seq (selectM c) (.seq (occurrence c) (.seq (incidence c)
        (.seq (prime c) (.seq (field c) (.seq (dimension c) (block c)))))))
      (fun n a => Known c n initialKnown a) (fun _ _ => True) := by
  let A1 := initialKnown ++ [23]
  let A2 := A1 ++ [24]
  let A3 := A2 ++ [16]
  let A4 := A3 ++ [6]
  let A5 := A4 ++ [17,25]
  let A6 := A5 ++ [19]
  have h1 := selectM_polynomial c initialKnown (by decide)
  have h2 := occurrence_polynomial c A1 (by simp [A1])
  have h3 := incidence_polynomial c A2
    (by simp [A2, A1, initialKnown]) (by simp [A2])
  have h4 := prime_polynomial c A3 (by simp [A3, A2, A1, initialKnown])
  have h5 := field_polynomial c A4 (by simp [A4]) (by simp [A4, A3])
  have h6 := dimension_polynomial c A5
    (by simp [A5, A4, A3, A2, A1, initialKnown])
    (by simp [A5, A4, A3, A2, A1, initialKnown])
  have h7 := block_polynomial c A6
    (by simp [A6, A5, A4, A3]) (by simp [A6, A5])
  exact h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7)))))

private theorem of_total_envelope (c : Config) (cmd : SetupCmd c)
    (hsem : ∀ a, ∃ t b, Eval cmd t a b)
    (hbound : ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ B P a t b,
      WordBound B a → Eval cmd t a b →
      t ≤ C * (B + P + 1) ^ q ∧ WordBound (C * (B + P + 1) ^ q) b) :
    PolynomialRun cmd (fun _ _ => True) (fun _ _ => True) := by
  apply of_unconditional_envelope c cmd _ _ _ hbound
  apply Filter.Eventually.of_forall
  intro n a _
  obtain ⟨t, b, he⟩ := hsem a
  exact ⟨t, b, he, trivial⟩

theorem precision_polynomial (c : Config) :
    PolynomialRun (precision c) (fun _ _ => True) (fun _ _ => True) := by
  apply of_total_envelope c (precision c)
  · intro a
    obtain ⟨t, _, he, _, _⟩ := counterStage_eval c true 19 22 a
    exact ⟨t, _, he⟩
  · exact SubexpSetupControlBounds.counterStage_envelope c true 19 22

theorem inverseExponent_polynomial (c : Config) :
    PolynomialRun (inverseExponent c) (fun _ _ => True) (fun _ _ => True) := by
  apply of_total_envelope c (inverseExponent c)
  · intro a
    obtain ⟨t, _, he, _, _⟩ := counterStage_eval c false 17 29 a
    exact ⟨t, _, he⟩
  · exact SubexpSetupControlBounds.counterStage_envelope c false 17 29

theorem colors_polynomial (c : Config) :
    PolynomialRun (colors c) (fun _ _ => True) (fun _ _ => True) := by
  apply of_total_envelope c (colors c)
  · intro a
    obtain ⟨t, b, he, _, _⟩ := colors_eval c a
    exact ⟨t, b, he⟩
  · exact SubexpSetupControlBounds.colors_envelope c

theorem cutoff_polynomial (c : Config) :
    PolynomialRun (cutoff c) (fun _ _ => True) (fun _ _ => True) := by
  apply of_total_envelope c (cutoff c)
  · intro a
    obtain ⟨t, b, he, _, _⟩ := cutoff_eval c a
    exact ⟨t, b, he⟩
  · exact SubexpSetupControlBounds.cutoff_envelope c

theorem thresholdTable_polynomial (c : Config) :
    PolynomialRun (thresholdTable c) (fun _ _ => True) (fun _ _ => True) := by
  apply of_total_envelope c (thresholdTable c)
  · intro a
    obtain ⟨t, rf, words, _, he, _, _, _⟩ := SubexpSetupPhaseTable.table_eval c a
    exact ⟨_, _, he⟩
  · exact SubexpSetupPhaseTable.thresholdTable_polynomial c

theorem readyGuard_polynomial (c : Config) :
    PolynomialRun (readyGuard c) (fun _ _ => True) (fun _ _ => True) :=
  of_total_envelope c (readyGuard c)
    (SubexpSetupControlBounds.readyGuard_total c)
    (SubexpSetupControlBounds.readyGuard_envelope c)

theorem cleanup_polynomial (c : Config) :
    PolynomialRun (clearMany (workspacePorts c)) (fun _ _ => True) (fun _ _ => True) := by
  apply of_total_envelope c (clearMany (workspacePorts c))
  · intro a
    exact ⟨_, _, clearMany_eval (workspacePorts c) a⟩
  · exact SubexpSetupControlBounds.cleanup_envelope c

/-- Every numerical phase is an actual measured execution. Values are needed
only up to the positive-divisor and growing-loop guards. -/
theorem numericSetup_polynomial (c : Config) :
    PolynomialRun (numericSetup c)
      (fun n a => Known c n initialKnown a) (fun _ _ => True) := by
  let A1 := initialKnown ++ [23]
  let A2 := A1 ++ [24]
  let A3 := A2 ++ [16]
  let A4 := A3 ++ [6]
  let A5 := A4 ++ [17,25]
  let A6 := A5 ++ [19]
  have h1 := selectM_polynomial c initialKnown (by decide)
  have h2 := occurrence_polynomial c A1 (by simp [A1])
  have h3 := incidence_polynomial c A2
    (by simp [A2, A1, initialKnown]) (by simp [A2])
  have h4 := prime_polynomial c A3 (by simp [A3, A2, A1, initialKnown])
  have h5 := field_polynomial c A4 (by simp [A4]) (by simp [A4, A3])
  have h6 := dimension_polynomial c A5
    (by simp [A5, A4, A3, A2, A1, initialKnown])
    (by simp [A5, A4, A3, A2, A1, initialKnown])
  have h7 := block_polynomial c A6
    (by simp [A6, A5, A4, A3]) (by simp [A6, A5])
  have hs := (tail_polynomial c).seq ((precision_polynomial c).seq
    ((inverseExponent_polynomial c).seq ((colors_polynomial c).seq (cutoff_polynomial c))))
  exact h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq hs))))))

theorem scalarSetup_polynomial (c : Config) :
    PolynomialRun (scalarSetup c)
      (fun n a => Known c n initialKnown a) (fun _ _ => True) :=
  (numericSetup_polynomial c).seq
    ((thresholdTable_polynomial c).seq (readyGuard_polynomial c))

/-- The implemented early guard accepts on the proved eventual domain and
preserves the three schedule words consumed by numerical setup. -/
theorem early_polynomial (c : Config) :
    PolynomialRun (early c) (fun n a => Known c n initialKnown a)
      (fun n b => Known c n initialKnown b ∧ b.regs 15 = true) := by
  apply of_unconditional_envelope c (early c) _ _ _
    (SubexpSetupControlBounds.early_envelope c)
  filter_upwards [SubexpPackingParameters.eventually_goodInput] with n hn
  intro a hk
  obtain ⟨t, b, he, hflag, hf⟩ := early_eval c a
  refine ⟨t, b, he, known_frame c n initialKnown a b hk
    (fun i => hf _ (persistent_protected c i)), ?_⟩
  apply hflag.mpr
  have hs : BinaryArithmetic.toNat (a.stacks (persistent c 4)) =
      SubexpPackingParameters.s n := hk 4 (by decide)
  rw [hs]
  exact hn

theorem scalarCommand_polynomial (c : Config) :
    PolynomialRun (scalarCommand c)
      (fun n a => Known c n initialKnown a) (fun _ _ => True) := by
  have hs : PolynomialRun (scalarSetup c)
      (fun n a => Known c n initialKnown a ∧ a.regs 15 = true)
      (fun _ _ => True) :=
    (scalarSetup_polynomial c).mono (fun _ _ h => h.1) (fun _ _ h => h)
  exact (early_polynomial c).seq (hs.ite_true (fun _ _ h => h.2))

theorem command_polynomial (c : Config) :
    PolynomialRun (command c)
      (fun n a => Known c n initialKnown a) (fun _ _ => True) :=
  (scalarCommand_polynomial c).seq (cleanup_polynomial c)

/-- One polynomial bounds the actual full setup trace and every output word.
The semantic conclusions come from the same deterministic execution. -/
theorem eventually_command_bounded (c : Config) :
    ∃ C d : ℕ, 1 ≤ C ∧ 1 ≤ d ∧
      ∀ᶠ n : ℕ in atTop, ∀ L a, n ≤ L → Known c n initialKnown a → WordBound L a →
        ∃ t b, Eval (command c) t a b ∧ t ≤ C * (L + 1) ^ d ∧
          WordBound (C * (L + 1) ^ d) b ∧
          (b.regs 15 = true ↔ DyadicSchedule.Ready c.k c.T n) ∧
          ScalarValues c n b ∧ ThresholdValues c n b ∧
          RetainedFrame c a b ∧ (∀ i, i.val < helperSize c → b.stacks i = []) := by
  obtain ⟨C, d, hC, hd, hrun⟩ := command_polynomial c
  refine ⟨C, d, hC, hd, ?_⟩
  filter_upwards [hrun, SubexpPackingParameters.eventually_goodInput] with n hrun hn
  intro L a hnL hk hw
  obtain ⟨t, b, he, ht, hb, _⟩ := hrun L a hnL hk hw
  obtain ⟨u, out, hu, hflag, hvalues, hframe, hclear⟩ := command_eval c n a hk
  have hsame := SubexpPrimeProgram.eval_result_unique he hu (persistent c 0) (persistent c 0)
  subst out
  exact ⟨t, b, he, ht, hb, hflag, (hvalues hn).1, (hvalues hn).2, hframe, hclear⟩

theorem eventually_program_bounded (c : Config) :
    ∃ C d : ℕ, 1 ≤ C ∧ 1 ≤ d ∧
      ∀ᶠ n : ℕ in atTop, ∀ L a, n ≤ L → Known c n initialKnown a → WordBound L a →
        ∃ t b, Trace (program c) t (a.withPC (some (program c).entry)) (b.withPC none) ∧
          t ≤ C * (L + 1) ^ d ∧ WordBound (C * (L + 1) ^ d) b ∧
          (b.regs 15 = true ↔ DyadicSchedule.Ready c.k c.T n) ∧
          ScalarValues c n b ∧ ThresholdValues c n b ∧
          RetainedFrame c a b ∧ (∀ i, i.val < helperSize c → b.stacks i = []) := by
  obtain ⟨C, d, hC, hd, hrun⟩ := eventually_command_bounded c
  refine ⟨C + 1, d, by omega, hd, ?_⟩
  filter_upwards [hrun] with n hrun
  intro L a hnL hk hw
  obtain ⟨t, b, he, ht, hb, hflag, hscalar, hthreshold, hframe, hclear⟩ := hrun L a hnL hk hw
  have hp : 1 ≤ (L + 1) ^ d := Nat.one_le_pow _ _ (by omega)
  have htime : t + 1 ≤ (C + 1) * (L + 1) ^ d := by
    calc
      t + 1 ≤ C * (L + 1) ^ d + (L + 1) ^ d := Nat.add_le_add ht hp
      _ = _ := by ring
  exact ⟨t + 1, b, compiled_halt_trace he (persistent c 0) (persistent c 0), htime,
    wordBound_mono hb (Nat.mul_le_mul_right _ (by omega)),
    hflag, hscalar, hthreshold, hframe, hclear⟩

end SubexponentialSAT.SubexpSetupRuntime

end OAI.Algorithms
