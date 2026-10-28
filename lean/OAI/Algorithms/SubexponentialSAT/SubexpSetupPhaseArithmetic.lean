import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupArithmeticLocal
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStages

namespace OAI.Algorithms

/-! Concrete arithmetic setup stages, including physical preparation and cleanup. -/
namespace SubexponentialSAT.SubexpSetupPhaseArithmetic

noncomputable section

open BitProgram StructuredCalls BinaryArithmetic
open SubexpSetupProgram SubexpSetupStorage

theorem prepared_io (c : Config) {r s : ℕ} (hr : r ≤ 9)
    (hs : s < helperSize c) (source : Fin 32) (target : Fin s) (a : SetupState c) :
    project (registerPort hr) (workPort c hs)
      (prepared c hs [(persistent c source, target)] a) =
      StructuredProgram.ioState target (a.stacks (persistent c source)) := by
  apply prepared_eq c (registerPort hr) hs [(persistent c source, target)] a _
    (by simp) (by simp)
  · intro j
    exact prepared_register c hr hs _ a j
  · intro p hp
    obtain rfl := List.mem_singleton.mp hp
    simp []
  · intro j hj
    have hne : j ≠ target := hj (persistent c source, target) (by simp)
    simp [ hne]

def pairInput {r s : ℕ} (first second : Fin s) (xs ys : List Bool) :
    StructuredProgram.State r s :=
  ⟨fun _ => false, fun j => if j = second then ys else if j = first then xs else []⟩

theorem prepared_pair (c : Config) {r s : ℕ} (hr : r ≤ 9)
    (hs : s < helperSize c) (source₁ source₂ : Fin 32) (target₁ target₂ : Fin s)
    (hne : target₁ ≠ target₂) (a : SetupState c) :
    project (registerPort hr) (workPort c hs)
      (prepared c hs [(persistent c source₁, target₁), (persistent c source₂, target₂)] a) =
      pairInput target₁ target₂ (a.stacks (persistent c source₁))
        (a.stacks (persistent c source₂)) := by
  apply prepared_eq c (registerPort hr) hs _ a _ (by simp) (by simp [hne])
  · intro j
    exact prepared_register c hr hs _ a j
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [pairInput, hne]
  · intro j hj
    have h₁ : j ≠ target₁ := hj (persistent c source₁, target₁) (by simp)
    have h₂ : j ≠ target₂ := hj (persistent c source₂, target₂) (by simp)
    simp [pairInput, h₁, h₂]

def selectResult (c : Config) (a : SetupState c) : SetupState c :=
  returned c (registerPort (by decide : 3 ≤ 9)) (small_fits c (by decide : 3 ≤ 32))
    [(persistent c 4, 0)] [(2, persistent c 23)] a
    (selectOutput c.T (a.stacks (persistent c 4)))

def selectCost (c : Config) (a : SetupState c) : ℕ :=
  stageCost c (registerPort (by decide : 3 ≤ 9)) (small_fits c (by decide : 3 ≤ 32))
    [(persistent c 4, 0)] [(2, persistent c 23)] a
    (selectOutput c.T (a.stacks (persistent c 4)))
    (SparsificationBudgetProgram.runtimeBound c.T (a.stacks (persistent c 4)).length)

theorem selectResult_word (c : Config) (a : SetupState c) :
    (selectResult c a).stacks (persistent c 23) =
      SparsificationBudgetProgram.outputWord c.T (BinaryArithmetic.toNat (a.stacks (persistent c 4))) := by
  have hw := returned_word c (registerPort (by decide : 3 ≤ 9))
    (small_fits c (by decide : 3 ≤ 32)) [(persistent c 4, 0)] [(2, persistent c 23)]
    a (selectOutput c.T (a.stacks (persistent c 4))) (by simp) (by simp)
    (2, persistent c 23) (by simp)
  change (selectResult c a).stacks (persistent c 23) =
    SparsificationBudgetProgram.outputWord c.T (CounterPrograms.value (a.stacks (persistent c 4))) at hw
  simpa only [SubexpParameterProgram.value_eq_toNat] using hw

theorem selectResult_word_schedule (c : Config) (n : ℕ) (a : SetupState c)
    (hs : BinaryArithmetic.toNat (a.stacks (persistent c 4)) = SubexpPackingParameters.s n) :
    (selectResult c a).stacks (persistent c 23) =
      SparsificationBudgetProgram.outputWord c.T (SubexpPackingParameters.s n) := by
  simpa only [hs] using selectResult_word c a

theorem selectM_eval (c : Config) (a : SetupState c) :
    ∃ t, t ≤ selectCost c a ∧ Eval (selectM c) t a (selectResult c a) ∧
      BinaryArithmetic.toNat ((selectResult c a).stacks (persistent c 23)) =
        SparsificationBudgetProgram.dyadicM c.T (BinaryArithmetic.toNat (a.stacks (persistent c 4))) ∧
      ((selectResult c a).stacks (persistent c 23)).length ≤
        c.T + 2 * (a.stacks (persistent c 4)).length + 3 ∧
      Preserves c [persistent c 23] a (selectResult c a) := by
  obtain ⟨t, ht, htime, hv, hl⟩ := select_local c.T (a.stacks (persistent c 4))
  have hp := prepared_io c (by decide : 3 ≤ 9) (small_fits c (by decide : 3 ≤ 32)) 4 0 a
  have he := stage_eval c (SparsificationBudgetProgram.program c.T)
    (registerPort (by decide : 3 ≤ 9)) (registerPort_injective (by decide))
    (small_fits c (by decide : 3 ≤ 32)) [(persistent c 4, 0)] [(2, persistent c 23)]
    a _ _ (by simp) (by simp) hp ht
  have hw := returned_word c (registerPort (by decide : 3 ≤ 9))
    (small_fits c (by decide : 3 ≤ 32)) [(persistent c 4, 0)] [(2, persistent c 23)]
    a (selectOutput c.T (a.stacks (persistent c 4))) (by simp) (by simp)
    (2, persistent c 23) (by simp)
  refine ⟨_, ?_, he, ?_, ?_, ?_⟩
  · unfold selectCost stageCost
    omega
  · exact (congrArg BinaryArithmetic.toNat hw).trans hv
  · exact (congrArg List.length hw).trans_le hl
  · exact returned_preserves c (by decide : 3 ≤ 9)
      (small_fits c (by decide : 3 ≤ 32)) _ _ a _

theorem occurrenceInput_eq_io (k : ℕ) (xs : List Bool) :
    occurrenceInput k xs = StructuredProgram.ioState
      (ArithmeticExpressionProgram.inputPort
        (show 2 ≤ ArithmeticExpressionProgram.slots (SparsificationThresholdProgram.occurrenceExpr k)
          from le_trans (by decide) (ArithmeticExpressionProgram.slots_ge _))) xs := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  by_cases hi : i.val = 0 <;> by_cases ho : i.val = 1 <;>
    simp_all [
      ArithmeticExpressionProgram.inputPort, ArithmeticExpressionProgram.outputPort,
      Function.update_apply, Fin.ext_iff]

theorem occurrenceFits (c : Config) :
    ArithmeticExpressionProgram.slots (SparsificationThresholdProgram.occurrenceExpr c.k) <
      helperSize c := by unfold helperSize occurrenceSlots; omega

def occurrenceOut (c : Config) (a : SetupState c) (rf : Fin 8 → Bool) (word : List Bool) :=
  ArithmeticExpressionProgram.state
    (show 2 ≤ ArithmeticExpressionProgram.slots (SparsificationThresholdProgram.occurrenceExpr c.k)
      from le_trans (by decide) (ArithmeticExpressionProgram.slots_ge _))
    rf (a.stacks (persistent c 23)) word

def occurrenceResult (c : Config) (a : SetupState c) (rf : Fin 8 → Bool) (word : List Bool) :=
  returned c (registerPort (by decide : 8 ≤ 9)) (occurrenceFits c)
    [(persistent c 23, (SparsificationThresholdProgram.occurrenceProgram c.k).inputStack)]
    [((SparsificationThresholdProgram.occurrenceProgram c.k).outputStack, persistent c 24)]
    a (occurrenceOut c a rf word)

def occurrenceCost (c : Config) (a : SetupState c) (rf : Fin 8 → Bool) (word : List Bool) :=
  stageCost c (registerPort (by decide : 8 ≤ 9)) (occurrenceFits c)
    [(persistent c 23, (SparsificationThresholdProgram.occurrenceProgram c.k).inputStack)]
    [((SparsificationThresholdProgram.occurrenceProgram c.k).outputStack, persistent c 24)]
    a (occurrenceOut c a rf word)
    ((ArithmeticExpressionProgram.timeCoeff (SparsificationThresholdProgram.occurrenceExpr c.k) + 1) *
      ((a.stacks (persistent c 23)).length + 1) ^ 2)

theorem occurrence_eval (c : Config) (a : SetupState c) :
    ∃ t rf word, t ≤ occurrenceCost c a rf word ∧
      Eval (occurrence c) t a (occurrenceResult c a rf word) ∧
      BinaryArithmetic.toNat ((occurrenceResult c a rf word).stacks (persistent c 24)) =
        SparsificationConstants.occurrenceCap (BinaryArithmetic.toNat (a.stacks (persistent c 23))) c.k ∧
      ((occurrenceResult c a rf word).stacks (persistent c 24)).length ≤
        ArithmeticExpressionProgram.widthCoeff (SparsificationThresholdProgram.occurrenceExpr c.k) *
          ((a.stacks (persistent c 23)).length + 1) ∧
      Preserves c [persistent c 24] a (occurrenceResult c a rf word) := by
  obtain ⟨t, rf, word, ht, htime, hv, hl⟩ := occurrence_local c.k (a.stacks (persistent c 23))
  have hp := prepared_io c (by decide : 8 ≤ 9) (occurrenceFits c) 23
    (SparsificationThresholdProgram.occurrenceProgram c.k).inputStack a
  have hprepared := hp.trans (occurrenceInput_eq_io c.k (a.stacks (persistent c 23))).symm
  have he := stage_eval c (SparsificationThresholdProgram.occurrenceProgram c.k)
    (registerPort (by decide : 8 ≤ 9)) (registerPort_injective (by decide))
    (occurrenceFits c) [(persistent c 23, (SparsificationThresholdProgram.occurrenceProgram c.k).inputStack)]
    [((SparsificationThresholdProgram.occurrenceProgram c.k).outputStack, persistent c 24)]
    a _ _ (by simp) (by simp) hprepared ht
  have hw := returned_word c (registerPort (by decide : 8 ≤ 9)) (occurrenceFits c)
    [(persistent c 23, (SparsificationThresholdProgram.occurrenceProgram c.k).inputStack)]
    [((SparsificationThresholdProgram.occurrenceProgram c.k).outputStack, persistent c 24)]
    a (occurrenceOut c a rf word) (by simp) (by simp)
    ((SparsificationThresholdProgram.occurrenceProgram c.k).outputStack, persistent c 24) (by simp)
  change (occurrenceResult c a rf word).stacks (persistent c 24) = word at hw
  refine ⟨_, rf, word, ?_, he, ?_, ?_, ?_⟩
  · unfold occurrenceCost occurrenceOut stageCost
    omega
  · exact (congrArg BinaryArithmetic.toNat hw).trans hv
  · exact (congrArg List.length hw).trans_le hl
  · exact returned_preserves c (by decide : 8 ≤ 9) (occurrenceFits c) _ _ a _

theorem incidenceInput_eq_pair (ell cap : List Bool) :
    incidenceInput ell cap = pairInput 0 1 ell cap := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> rfl

def incidenceOut (c : Config) (a : SetupState c) (rf : Fin 8 → Bool) (word : List Bool) :
    SubexpIncidenceGuardProgram.Data :=
  ⟨rf, Function.update
    (incidenceInput (a.stacks (persistent c 5)) (a.stacks (persistent c 24))).stacks 2 word⟩

def incidenceResult (c : Config) (a : SetupState c) (rf : Fin 8 → Bool) (word : List Bool) :=
  returned c (registerPort (by decide : 8 ≤ 9)) (small_fits c (by decide : 10 ≤ 32))
    [(persistent c 5, 0), (persistent c 24, 1)] [(2, persistent c 16)] a (incidenceOut c a rf word)

def incidenceCost (c : Config) (a : SetupState c) (rf : Fin 8 → Bool) (word : List Bool) :=
  stageCost c (registerPort (by decide : 8 ≤ 9)) (small_fits c (by decide : 10 ≤ 32))
    [(persistent c 5, 0), (persistent c 24, 1)] [(2, persistent c 16)] a (incidenceOut c a rf word)
    (300 * ((a.stacks (persistent c 5)).length + (a.stacks (persistent c 24)).length + 3) ^ 2 + 1)

theorem incidence_eval (c : Config) (a : SetupState c) :
    ∃ t rf word, t ≤ incidenceCost c a rf word ∧
      Eval (incidence c) t a (incidenceResult c a rf word) ∧
      BinaryArithmetic.toNat ((incidenceResult c a rf word).stacks (persistent c 16)) =
        1 + BinaryArithmetic.toNat (a.stacks (persistent c 5)) * BinaryArithmetic.toNat (a.stacks (persistent c 24)) ∧
      ((incidenceResult c a rf word).stacks (persistent c 16)).length ≤
        (a.stacks (persistent c 5)).length + (a.stacks (persistent c 24)).length + 3 ∧
      Preserves c [persistent c 16] a (incidenceResult c a rf word) := by
  obtain ⟨t, rf, word, ht, htime, hv, hl⟩ :=
    incidence_local (a.stacks (persistent c 5)) (a.stacks (persistent c 24))
  have hp := prepared_pair c (by decide : 8 ≤ 9) (small_fits c (by decide : 10 ≤ 32))
    5 24 0 1 (by decide) a
  rw [← incidenceInput_eq_pair (a.stacks (persistent c 5)) (a.stacks (persistent c 24))] at hp
  have he := stage_eval c SubexpIncidenceGuardProgram.program
    (registerPort (by decide : 8 ≤ 9)) (registerPort_injective (by decide))
    (small_fits c (by decide : 10 ≤ 32)) [(persistent c 5, 0), (persistent c 24, 1)]
    [(2, persistent c 16)] a _ _ (by simp) (by simp) hp ht
  have hw := returned_word c (registerPort (by decide : 8 ≤ 9))
    (small_fits c (by decide : 10 ≤ 32)) [(persistent c 5, 0), (persistent c 24, 1)]
    [(2, persistent c 16)] a (incidenceOut c a rf word) (by simp) (by simp)
    (2, persistent c 16) (by simp)
  change (incidenceResult c a rf word).stacks (persistent c 16) = word at hw
  refine ⟨_, rf, word, ?_, he, ?_, ?_, ?_⟩
  · unfold incidenceCost incidenceOut stageCost
    omega
  · exact (congrArg BinaryArithmetic.toNat hw).trans hv
  · exact (congrArg List.length hw).trans_le hl
  · exact returned_preserves c (by decide : 8 ≤ 9) (small_fits c (by decide : 10 ≤ 32)) _ _ a _

def primeResult (c : Config) (a : SetupState c) (out : SubexpPrimeIntervalProgram.State) :=
  returned c (registerPort (by decide : 9 ≤ 9)) (small_fits c (by decide : 12 ≤ 32))
    [(persistent c 5, 0)] [(9, persistent c 6)] a out

def primeCost (c : Config) (a : SetupState c) (out : SubexpPrimeIntervalProgram.State) :=
  stageCost c (registerPort (by decide : 9 ≤ 9)) (small_fits c (by decide : 12 ≤ 32))
    [(persistent c 5, 0)] [(9, persistent c 6)] a out
    (SubexpPrimeSelectRuntime.selectorBound (a.stacks (persistent c 5)) + 1)

theorem prime_eval (c : Config) (a : SetupState c) :
    ∃ t out, t ≤ primeCost c a out ∧ Eval (prime c) t a (primeResult c a out) ∧
      BinaryArithmetic.toNat ((primeResult c a out).stacks (persistent c 6)) =
        SubexpPrimeIntervalProgram.selectedPrime (BinaryArithmetic.toNat (a.stacks (persistent c 5))) ∧
      ((primeResult c a out).stacks (persistent c 6)).length ≤
        SubexpPrimeSelectRuntime.endpointWordBound (a.stacks (persistent c 5)) +
          (2 ^ BinaryArithmetic.toNat (a.stacks (persistent c 5)) - 1) ∧
      (∀ i, (out.stacks i).length ≤
        SubexpPrimeSelectRuntime.selectorWordBound (a.stacks (persistent c 5))) ∧
      Preserves c [persistent c 6] a (primeResult c a out) := by
  obtain ⟨t, out, ht, htime, hv, hl, hAll⟩ := prime_local (a.stacks (persistent c 5))
  have hp := prepared_io c (by decide : 9 ≤ 9) (small_fits c (by decide : 12 ≤ 32)) 5 0 a
  have he := stage_eval c SubexpPrimeIntervalProgram.primeSelectProgram
    (registerPort (by decide : 9 ≤ 9)) (registerPort_injective (by decide))
    (small_fits c (by decide : 12 ≤ 32)) [(persistent c 5, 0)] [(9, persistent c 6)]
    a _ _ (by simp) (by simp) hp ht
  have hw := returned_word c (registerPort (by decide : 9 ≤ 9))
    (small_fits c (by decide : 12 ≤ 32)) [(persistent c 5, 0)] [(9, persistent c 6)]
    a out (by simp) (by simp) (9, persistent c 6) (by simp)
  refine ⟨_, out, ?_, he, ?_, ?_, hAll, ?_⟩
  · unfold primeCost stageCost
    omega
  · exact (congrArg BinaryArithmetic.toNat hw).trans hv
  · exact (congrArg List.length hw).trans_le hl
  · exact returned_preserves c (by decide : 9 ≤ 9) (small_fits c (by decide : 12 ≤ 32)) _ _ a _

theorem fieldInput_eq_pair (p delta : List Bool) : fieldInput p delta = pairInput 0 1 p delta := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  fin_cases i <;> rfl

def fieldResult (c : Config) (a : SetupState c) (out : SubexpFieldParameterProgram.Data) :=
  returned c (registerPort (by decide : 8 ≤ 9)) (small_fits c (by decide : 16 ≤ 32))
    [(persistent c 6, 0), (persistent c 16, 1)] [(4, persistent c 17), (7, persistent c 25)] a out

def fieldCost (c : Config) (a : SetupState c) (out : SubexpFieldParameterProgram.Data) :=
  stageCost c (registerPort (by decide : 8 ≤ 9)) (small_fits c (by decide : 16 ≤ 32))
    [(persistent c 6, 0), (persistent c 16, 1)] [(4, persistent c 17), (7, persistent c 25)] a out
    (30000 * (SubexpFieldParameterProgram.width c.k
      (a.stacks (persistent c 6)) (a.stacks (persistent c 16))) ^ 2)

theorem field_eval (c : Config) (a : SetupState c)
    (hp : 0 < BinaryArithmetic.toNat (a.stacks (persistent c 6))) (hd : 0 < BinaryArithmetic.toNat (a.stacks (persistent c 16))) :
    ∃ t out, t ≤ fieldCost c a out ∧ Eval (field c) t a (fieldResult c a out) ∧
      BinaryArithmetic.toNat ((fieldResult c a out).stacks (persistent c 17)) =
        BinaryArithmetic.toNat (a.stacks (persistent c 6)) ^ 4 - 1 ∧
      BinaryArithmetic.toNat ((fieldResult c a out).stacks (persistent c 25)) =
        (BinaryArithmetic.toNat (a.stacks (persistent c 6)) ^ 4 - 1) /
          (8 * BinaryArithmetic.toNat (a.stacks (persistent c 16)) * c.k * BinaryArithmetic.toNat (a.stacks (persistent c 6))) ∧
      ((fieldResult c a out).stacks (persistent c 17)).length ≤
        4 * SubexpFieldParameterProgram.width c.k
          (a.stacks (persistent c 6)) (a.stacks (persistent c 16)) ∧
      ((fieldResult c a out).stacks (persistent c 25)).length ≤
        4 * SubexpFieldParameterProgram.width c.k
          (a.stacks (persistent c 6)) (a.stacks (persistent c 16)) ∧
      (∀ i, (out.stacks i).length ≤ 4 * SubexpFieldParameterProgram.width c.k
        (a.stacks (persistent c 6)) (a.stacks (persistent c 16))) ∧
      Preserves c [persistent c 17, persistent c 25] a (fieldResult c a out) := by
  have hk : 0 < c.k := by have := c.width_ge_two; omega
  obtain ⟨t, out, ht, htime, hQ, hR, hl⟩ :=
    field_local c.k hk (a.stacks (persistent c 6)) (a.stacks (persistent c 16)) hp hd
  have hprepared := prepared_pair c (by decide : 8 ≤ 9) (small_fits c (by decide : 16 ≤ 32))
    6 16 0 1 (by decide) a
  rw [← fieldInput_eq_pair (a.stacks (persistent c 6)) (a.stacks (persistent c 16))] at hprepared
  have he := stage_eval c (SubexpFieldParameterProgram.program c.k)
    (registerPort (by decide : 8 ≤ 9)) (registerPort_injective (by decide))
    (small_fits c (by decide : 16 ≤ 32))
    [(persistent c 6, 0), (persistent c 16, 1)] [(4, persistent c 17), (7, persistent c 25)]
    a _ _ (by simp) (by simp) hprepared ht
  have hnodup : ([persistent c 17, persistent c 25] : List (Fin (stackCount c))).Nodup := by
    simp [persistent, Fin.ext_iff]
  have hwQ := returned_word c (registerPort (by decide : 8 ≤ 9))
    (small_fits c (by decide : 16 ≤ 32))
    [(persistent c 6, 0), (persistent c 16, 1)] [(4, persistent c 17), (7, persistent c 25)]
    a out (by simp) hnodup (4, persistent c 17) (by simp)
  have hwR := returned_word c (registerPort (by decide : 8 ≤ 9))
    (small_fits c (by decide : 16 ≤ 32))
    [(persistent c 6, 0), (persistent c 16, 1)] [(4, persistent c 17), (7, persistent c 25)]
    a out (by simp) hnodup (7, persistent c 25) (by simp)
  refine ⟨_, out, ?_, he, (congrArg BinaryArithmetic.toNat hwQ).trans hQ, (congrArg BinaryArithmetic.toNat hwR).trans hR,
    (congrArg List.length hwQ).trans_le (hl 4), (congrArg List.length hwR).trans_le (hl 7), hl, ?_⟩
  · unfold fieldCost stageCost
    omega
  · exact returned_preserves c (by decide : 8 ≤ 9) (small_fits c (by decide : 16 ≤ 32)) _ _ a _

theorem selectM_schedule (c : Config) (n : ℕ) (a : SetupState c)
    (hs : BinaryArithmetic.toNat (a.stacks (persistent c 4)) = SubexpPackingParameters.s n) :
    ∃ t, t ≤ selectCost c a ∧ Eval (selectM c) t a (selectResult c a) ∧
      BinaryArithmetic.toNat ((selectResult c a).stacks (persistent c 23)) = DyadicSchedule.M c.T n ∧
      ((selectResult c a).stacks (persistent c 23)).length ≤
        c.T + 2 * (a.stacks (persistent c 4)).length + 3 ∧
      Preserves c [persistent c 23] a (selectResult c a) := by
  obtain ⟨t, ht, he, hv, hl, hf⟩ := selectM_eval c a
  exact ⟨t, ht, he, by simpa only [hs, DyadicSchedule.M] using hv, hl, hf⟩

theorem occurrence_schedule (c : Config) (n : ℕ) (a : SetupState c)
    (hM : BinaryArithmetic.toNat (a.stacks (persistent c 23)) = DyadicSchedule.M c.T n) :
    ∃ t rf word, t ≤ occurrenceCost c a rf word ∧
      Eval (occurrence c) t a (occurrenceResult c a rf word) ∧
      BinaryArithmetic.toNat ((occurrenceResult c a rf word).stacks (persistent c 24)) = DyadicSchedule.B c.k c.T n ∧
      ((occurrenceResult c a rf word).stacks (persistent c 24)).length ≤
        ArithmeticExpressionProgram.widthCoeff (SparsificationThresholdProgram.occurrenceExpr c.k) *
          ((a.stacks (persistent c 23)).length + 1) ∧
      Preserves c [persistent c 24] a (occurrenceResult c a rf word) := by
  obtain ⟨t, rf, word, ht, he, hv, hl, hf⟩ := occurrence_eval c a
  exact ⟨t, rf, word, ht, he, by simpa only [hM, DyadicSchedule.B] using hv, hl, hf⟩

theorem incidence_schedule (c : Config) (n : ℕ) (a : SetupState c)
    (hell : BinaryArithmetic.toNat (a.stacks (persistent c 5)) = SubexpPackingParameters.ell n)
    (hB : BinaryArithmetic.toNat (a.stacks (persistent c 24)) = DyadicSchedule.B c.k c.T n) :
    ∃ t rf word, t ≤ incidenceCost c a rf word ∧
      Eval (incidence c) t a (incidenceResult c a rf word) ∧
      BinaryArithmetic.toNat ((incidenceResult c a rf word).stacks (persistent c 16)) = DyadicSchedule.delta c.k c.T n ∧
      ((incidenceResult c a rf word).stacks (persistent c 16)).length ≤
        (a.stacks (persistent c 5)).length + (a.stacks (persistent c 24)).length + 3 ∧
      Preserves c [persistent c 16] a (incidenceResult c a rf word) := by
  obtain ⟨t, rf, word, ht, he, hv, hl, hf⟩ := incidence_eval c a
  exact ⟨t, rf, word, ht, he, by simpa only [hell, hB, DyadicSchedule.delta] using hv, hl, hf⟩

theorem prime_schedule (c : Config) (n : ℕ) (a : SetupState c)
    (hu : BinaryArithmetic.toNat (a.stacks (persistent c 5)) = SubexpPackingParameters.u n) :
    ∃ t out, t ≤ primeCost c a out ∧ Eval (prime c) t a (primeResult c a out) ∧
      BinaryArithmetic.toNat ((primeResult c a out).stacks (persistent c 6)) = SubexpPackingParameters.p n ∧
      ((primeResult c a out).stacks (persistent c 6)).length ≤
        SubexpPrimeSelectRuntime.endpointWordBound (a.stacks (persistent c 5)) +
          (2 ^ BinaryArithmetic.toNat (a.stacks (persistent c 5)) - 1) ∧
      Preserves c [persistent c 6] a (primeResult c a out) := by
  obtain ⟨t, out, ht, he, hv, hl, _, hf⟩ := prime_eval c a
  rw [hu, SubexpPrimeIntervalProgram.selectedPrime_eq_schedule] at hv
  exact ⟨t, out, ht, he, hv, hl, hf⟩

theorem field_schedule (c : Config) (n : ℕ) (a : SetupState c)
    (hp : BinaryArithmetic.toNat (a.stacks (persistent c 6)) = SubexpPackingParameters.p n)
    (hd : BinaryArithmetic.toNat (a.stacks (persistent c 16)) = DyadicSchedule.delta c.k c.T n) :
    ∃ t out, t ≤ fieldCost c a out ∧ Eval (field c) t a (fieldResult c a out) ∧
      BinaryArithmetic.toNat ((fieldResult c a out).stacks (persistent c 17)) = DyadicSchedule.Q n ∧
      BinaryArithmetic.toNat ((fieldResult c a out).stacks (persistent c 25)) = DyadicSchedule.R c.k c.T n ∧
      ((fieldResult c a out).stacks (persistent c 17)).length ≤
        4 * SubexpFieldParameterProgram.width c.k
          (a.stacks (persistent c 6)) (a.stacks (persistent c 16)) ∧
      ((fieldResult c a out).stacks (persistent c 25)).length ≤
        4 * SubexpFieldParameterProgram.width c.k
          (a.stacks (persistent c 6)) (a.stacks (persistent c 16)) ∧
      (∀ i, (out.stacks i).length ≤ 4 * SubexpFieldParameterProgram.width c.k
        (a.stacks (persistent c 6)) (a.stacks (persistent c 16))) ∧
      Preserves c [persistent c 17, persistent c 25] a (fieldResult c a out) := by
  have hp' : 0 < BinaryArithmetic.toNat (a.stacks (persistent c 6)) := by
    rw [hp]
    have := SubexpPackingParameters.p_gt_two n
    omega
  have hd' : 0 < BinaryArithmetic.toNat (a.stacks (persistent c 16)) := by
    rw [hd]
    exact DyadicSchedule.delta_pos c.k c.T n
  obtain ⟨t, out, ht, he, hQ, hR, hlQ, hlR, hAll, hf⟩ := field_eval c a hp' hd'
  refine ⟨t, out, ht, he, ?_, ?_, hlQ, hlR, hAll, hf⟩
  · simpa only [hp, DyadicSchedule.Q, SubexpParameters.sizeQ] using hQ
  · simpa only [hp, hd, DyadicSchedule.R, SubexpParameters.degreeR, SubexpParameters.sizeQ] using hR

end

end SubexponentialSAT.SubexpSetupPhaseArithmetic

end OAI.Algorithms
