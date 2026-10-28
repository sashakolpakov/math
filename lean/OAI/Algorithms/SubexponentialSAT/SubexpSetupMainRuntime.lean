import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupRuntime
import OAI.Algorithms.SubexponentialSAT.SubexpSetupMainExecution

namespace OAI.Algorithms

/-!
# Polynomial bounds for the actual raw-input numerical setup

The frontend and numerical setup below are the existing fixed instruction
tables. The final theorem starts with a canonical CNF encoding and has no
hypotheses about precomputed parameter words. All word bounds concern actual
bit lists, including padding.
-/

namespace SubexponentialSAT.SubexpSetupMainRuntime

open BitProgram StructuredCalls Filter
open SubexpSetupStorage SubexpSetupProgram SubexpMainProgram

/-- The numerical results in the installed Main state, together with the
retained fields and the cleared helper workspace. -/
structure Postconditions (c : Config) (er n : ℕ)
    (before : MainState er (mainExtraStacks c)) (out : SetupState c) : Prop where
  ready : ((mainProcedure c er).install before out).regs
      ((mainProcedure c er).registerMap (15 : Fin 16)) = true ↔ DyadicSchedule.Ready c.k c.T n
  scalar : ScalarValues c n out
  thresholds : ThresholdValues c n out
  retained : ∀ i : Fin 32, Retained i →
    ((mainProcedure c er).install before out).stacks
        (SubexpMainProgram.persistent (mainExtraStacks c) i) =
      before.stacks (SubexpMainProgram.persistent (mainExtraStacks c) i)
  clear : ∀ i : Fin (stackCount c), i.val < helperSize c →
    ((mainProcedure c er).install before out).stacks (mainStack c i) = []

theorem project_wordBound (c : Config) (er L : ℕ)
    (a : MainState er (mainExtraStacks c)) (ha : WordBound L a) :
    WordBound L ((mainProcedure c er).project a) := by
  intro i
  exact ha ((mainProcedure c er).stack i)

theorem initial_wordBound (er es : ℕ) (input : List Bool) :
    WordBound input.length (initialData er es input) := by
  intro i
  change (if i = SubexpMainProgram.persistent es 0 then input else []).length ≤ input.length
  split <;> simp

/-- Lifting a measured local trace preserves its instruction count. The
global word bound additionally accounts for every untouched caller word. -/
theorem eventually_main_bounded (c : Config) (er : ℕ) :
    ∃ C d : ℕ, 1 ≤ C ∧ 1 ≤ d ∧
      ∀ᶠ n : ℕ in atTop, ∀ L (a : MainState er (mainExtraStacks c)),
        n ≤ L → Known c n initialKnown ((mainProcedure c er).project a) → WordBound L a →
        ∃ t out, Eval (mainProcedure c er).invoke t a ((mainProcedure c er).install a out) ∧
          t ≤ C * (L + 1) ^ d ∧
          WordBound (C * (L + 1) ^ d) ((mainProcedure c er).install a out) ∧
          Postconditions c er n a out := by
  obtain ⟨C, d, hC, hd, hrun⟩ := SubexpSetupRuntime.eventually_program_bounded c
  refine ⟨C + 1, d, by omega, hd, ?_⟩
  filter_upwards [hrun] with n hrun
  intro L a hnL hk ha
  obtain ⟨t, out, ht, htime, _, hready, hscalar, hthreshold, hframe, hclear⟩ :=
    hrun L ((mainProcedure c er).project a) hnL hk (project_wordBound c er L a ha)
  have he := (mainProcedure c er).invoke_trace a out ht
  have hLP : L ≤ (L + 1) ^ d :=
    (Nat.le_succ L).trans (Nat.le_self_pow (by omega) (L + 1))
  have hsize : L + t ≤ (C + 1) * (L + 1) ^ d := by
    calc
      L + t ≤ (L + 1) ^ d + C * (L + 1) ^ d := Nat.add_le_add hLP htime
      _ = (C + 1) * (L + 1) ^ d := by ring
  refine ⟨t, out, he, htime.trans (Nat.mul_le_mul_right _ (by omega)),
    SubexpSetupBoundSpec.wordBound_mono (SubexpSetupBoundSpec.eval_wordBound ha he) hsize, ?_⟩
  refine ⟨?_, hscalar, hthreshold, ?_, ?_⟩
  · rw [main_install_flag]
    exact hready
  · intro i hi
    rw [main_install_word, hframe i hi, main_project_word]
  · intro i hi
    exact (embedState_stack _ _ _ _ (mainProcedure c er).stack.injective i).trans (hclear i hi)

private theorem prefix_word (er es : ℕ) (input body nb sb ub : List Bool) (i : Fin 6) :
    (prefixData er es input body nb sb ub).stacks
      (SubexpMainProgram.persistent es (i.castAdd 26)) =
      (SubexpFrontendPrefix.state body nb sb ub).stacks i :=
  embedState_stack _ _ _ _ (frontendProcedure er es).stack.injective i

private theorem prefix_known (c : Config) (er n : ℕ)
    (input body nb sb ub : List Bool)
    (hn : CounterPrograms.value nb = n)
    (hs : CounterPrograms.value sb = SubexpPackingParameters.s n)
    (hu : CounterPrograms.value ub = SubexpPackingParameters.u n) :
    Known c n initialKnown ((mainProcedure c er).project
      (prefixData er (mainExtraStacks c) input body nb sb ub)) := by
  apply initialKnown_of_words c n _
  · rw [main_project_word]
    rw [show (prefixData er (mainExtraStacks c) input body nb sb ub).stacks
        (SubexpMainProgram.persistent (mainExtraStacks c) 2) = nb from
      prefix_word er (mainExtraStacks c) input body nb sb ub 2]
    simpa only [CounterPrograms.value_eq_toNat] using hn
  · rw [main_project_word]
    rw [show (prefixData er (mainExtraStacks c) input body nb sb ub).stacks
        (SubexpMainProgram.persistent (mainExtraStacks c) 4) = sb from
      prefix_word er (mainExtraStacks c) input body nb sb ub 4]
    simpa only [CounterPrograms.value_eq_toNat] using hs
  · rw [main_project_word]
    rw [show (prefixData er (mainExtraStacks c) input body nb sb ub).stacks
        (SubexpMainProgram.persistent (mainExtraStacks c) 5) = ub from
      prefix_word er (mainExtraStacks c) input body nb sb ub 5]
    simpa only [CounterPrograms.value_eq_toNat] using hu

theorem prefix_bound_polynomial (L : ℕ) :
    SubexpFrontendPrefix.bound L ≤ 133 * (L + 1) ^ 2 := by
  rw [SubexpFrontendPrefix.bound_eq]
  nlinarith

theorem prefix_growth_polynomial (L : ℕ) :
    L + SubexpFrontendPrefix.bound L + 1 ≤ 135 * (L + 1) ^ 2 := by
  rw [SubexpFrontendPrefix.bound_eq]
  nlinarith

/-- A segmented execution certificate, suitable for the existing Main
controller. Every parameter word is produced by the actual frontend trace. -/
theorem eventually_raw_bounded (c : Config) (er : ℕ) :
    ∃ C d : ℕ, 1 ≤ C ∧ 1 ≤ d ∧
      ∀ᶠ n : ℕ in atTop, ∀ F : SAT.CNF (Fin n),
        ∃ (prefixSteps setupSteps : ℕ) (before : MainState er (mainExtraStacks c))
          (out : SetupState c),
          prefixSteps ≤ SubexpFrontendPrefix.bound (Encoding.formulaBitLength F) ∧
          Eval (frontendProcedure er (mainExtraStacks c)).invoke prefixSteps
            (initialData er (mainExtraStacks c) (Encoding.encodeCNF F)) before ∧
          Eval (mainProcedure c er).invoke setupSteps before ((mainProcedure c er).install before out) ∧
          prefixSteps + setupSteps ≤ C * (Encoding.formulaBitLength F + 1) ^ d ∧
          WordBound (C * (Encoding.formulaBitLength F + 1) ^ d)
            ((mainProcedure c er).install before out) ∧
          Postconditions c er n before out := by
  obtain ⟨C, d, hC, hd, hmain⟩ := eventually_main_bounded c er
  refine ⟨133 + C * 135 ^ d, 2 * d, by omega, by omega, ?_⟩
  filter_upwards [hmain] with n hmain
  intro F
  let L := Encoding.formulaBitLength F
  let M := L + SubexpFrontendPrefix.bound L
  obtain ⟨nb, sb, ub, tp, hn, hs, hu, hp, ep⟩ := prefix_execution er (mainExtraStacks c) F
  let before := prefixData er (mainExtraStacks c) (Encoding.encodeCNF F)
    (Encoding.encodeCNFBody F) nb sb ub
  have hinit : WordBound L (initialData er (mainExtraStacks c) (Encoding.encodeCNF F)) :=
    initial_wordBound er (mainExtraStacks c) (Encoding.encodeCNF F)
  have hbefore : WordBound M before := SubexpSetupBoundSpec.wordBound_mono
    (SubexpSetupBoundSpec.eval_wordBound hinit ep) (Nat.add_le_add_left hp L)
  have hnL : n ≤ L := Encoding.numVariables_le_formulaBitLength F
  have hnM : n ≤ M := hnL.trans (by dsimp [M]; omega)
  have hknown : Known c n initialKnown ((mainProcedure c er).project before) :=
    prefix_known c er n _ _ nb sb ub hn hs hu
  obtain ⟨ts, out, es, htime, hword, hpost⟩ := hmain M before hnM hknown hbefore
  have hgrowth : M + 1 ≤ 135 * (L + 1) ^ 2 := prefix_growth_polynomial L
  have hsetup : C * (M + 1) ^ d ≤ C * 135 ^ d * (L + 1) ^ (2 * d) := by
    calc
      _ ≤ C * (135 * (L + 1) ^ 2) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgrowth d)
      _ = C * 135 ^ d * (L + 1) ^ (2 * d) := by
        rw [mul_pow, ← pow_mul]
        ring
  have hpow : (L + 1) ^ 2 ≤ (L + 1) ^ (2 * d) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hprefix : tp ≤ 133 * (L + 1) ^ (2 * d) :=
    hp.trans ((prefix_bound_polynomial L).trans (Nat.mul_le_mul_left _ hpow))
  have htotal : tp + ts ≤ (133 + C * 135 ^ d) * (L + 1) ^ (2 * d) := by
    calc
      tp + ts ≤ 133 * (L + 1) ^ (2 * d) + C * 135 ^ d * (L + 1) ^ (2 * d) :=
        Nat.add_le_add hprefix (htime.trans hsetup)
      _ = (133 + C * 135 ^ d) * (L + 1) ^ (2 * d) := by ring
  have hout : WordBound ((133 + C * 135 ^ d) * (L + 1) ^ (2 * d))
      ((mainProcedure c er).install before out) :=
    SubexpSetupBoundSpec.wordBound_mono hword
      (hsetup.trans (Nat.mul_le_mul_right _ (by omega)))
  exact ⟨tp, ts, before, out, hp, ep, es, htotal, hout, hpost⟩

/-- The actual frontend followed by the actual numerical setup. -/
def rawCommand (c : Config) (er : ℕ) : MainCmd er (mainExtraStacks c) :=
  .seq (frontendProcedure er (mainExtraStacks c)).invoke (mainProcedure c er).invoke

/-- The same certificate as one executed Main command. Constants and the
eventual cutoff are fixed before the varying formula and its encoding. -/
theorem eventually_raw_execution (c : Config) (er : ℕ) :
    ∃ C d : ℕ, 1 ≤ C ∧ 1 ≤ d ∧
      ∀ᶠ n : ℕ in atTop, ∀ F : SAT.CNF (Fin n),
        ∃ (t : ℕ) (before : MainState er (mainExtraStacks c)) (out : SetupState c),
          Eval (rawCommand c er) t (initialData er (mainExtraStacks c) (Encoding.encodeCNF F))
            ((mainProcedure c er).install before out) ∧
          t ≤ C * (Encoding.formulaBitLength F + 1) ^ d ∧
          WordBound (C * (Encoding.formulaBitLength F + 1) ^ d)
            ((mainProcedure c er).install before out) ∧
          Postconditions c er n before out := by
  obtain ⟨C, d, hC, hd, hrun⟩ := eventually_raw_bounded c er
  refine ⟨C, d, hC, hd, ?_⟩
  filter_upwards [hrun] with n hrun
  intro F
  obtain ⟨tp, ts, before, out, _, ep, es, ht, hw, hpost⟩ := hrun F
  exact ⟨tp + ts, before, out, .seq ep es, ht, hw, hpost⟩

end SubexponentialSAT.SubexpSetupMainRuntime

end OAI.Algorithms
