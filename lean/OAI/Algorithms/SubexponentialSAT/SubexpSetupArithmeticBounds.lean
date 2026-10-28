import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupPhaseArithmetic
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost

namespace OAI.Algorithms

/-!
# Polynomial bounds for the five concrete arithmetic setup phases

The bounds below apply to every actual execution.  They include physical
preparation and cleanup and bound all final stack words, including padding.
The prime selector is parameterized by a bound on its actual interval scale.
-/

namespace SubexponentialSAT.SubexpSetupArithmeticBounds

open BitProgram StructuredCalls BinaryArithmetic
open SubexpSetupProgram SubexpSetupStorage SubexpSetupPhaseArithmetic

private theorem wordBound_mono {r s B C : ℕ} {a : State r s}
    (h : WordBound B a) (hBC : B ≤ C) : WordBound C a :=
  fun i => (h i).trans hBC

private theorem transfer {c : Config} {cmd : SetupCmd c} {a b d : SetupState c}
    {t n L : ℕ} (he : Eval cmd t a b) (hd : Eval cmd n a d)
    (hn : n ≤ L) (hw : WordBound L d) : t ≤ L ∧ WordBound L b := by
  have ht := SubexpPrimeProgram.eval_steps_unique he hd (persistent c 0) (persistent c 0)
  have hb := SubexpPrimeProgram.eval_result_unique he hd (persistent c 0) (persistent c 0)
  exact ⟨ht.trans_le hn, by simpa only [hb] using hw⟩

/-- A fixed coefficient absorbing the actual copy and cleanup loops. -/
def coefficient (ports inputs outputs width time : ℕ) : ℕ :=
  time + (6 * ports + 7 * inputs + 10 * outputs + 22) * (width + 1)

theorem coefficient_ge_width (ports inputs outputs width time : ℕ) :
    width + 1 ≤ coefficient ports inputs outputs width time := by
  have h := Nat.mul_le_mul_right (width + 1)
    (show 1 ≤ 6 * ports + 7 * inputs + 10 * outputs + 22 by omega)
  simp only [one_mul] at h
  unfold coefficient
  omega

theorem coefficient_pos (ports inputs outputs width time : ℕ) :
    1 ≤ coefficient ports inputs outputs width time :=
  le_trans (by omega) (coefficient_ge_width ports inputs outputs width time)

private theorem linear_le (a b z X : ℕ) (hz : z ≤ X) (hX : 1 ≤ X) :
    a * z + b ≤ (a + b) * X := by
  calc
    a * z + b ≤ a * X + b * X := Nat.add_le_add
      (Nat.mul_le_mul_left _ hz) (by simpa only [mul_one] using Nat.mul_le_mul_left b hX)
    _ = (a + b) * X := by ring

private theorem stage_bound (c : Config) {r s : ℕ} (register : Fin r → Fin 16)
    (hs : s < helperSize c) (inputs : List (Fin (stackCount c) × Fin s))
    (outputs : List (Fin s × Fin (stackCount c))) (a : SetupState c)
    (out : State r s) (time X W T q : ℕ)
    (hi : ∀ p ∈ inputs, Protected c p.1) (ho : ∀ p ∈ outputs, Protected c p.2)
    (hdi : (inputs.map Prod.snd).Nodup) (hdo : (outputs.map Prod.snd).Nodup)
    (hX : 1 ≤ X) (hW : 1 ≤ W) (hq : 1 ≤ q)
    (ha : WordBound X a) (hout : WordBound (W * X) out)
    (ht : time ≤ T * X ^ q) :
    stageCost c register hs inputs outputs a out time ≤
        coefficient s inputs.length outputs.length W T * X ^ q ∧
      WordBound (coefficient s inputs.length outputs.length W T * X ^ q)
        (returned c register hs inputs outputs a out) := by
  have hXP : X ≤ X ^ q := Nat.le_self_pow (by omega) X
  have h1P : 1 ≤ X ^ q := hX.trans hXP
  have ha' : WordBound (W * X) a := wordBound_mono ha
    (by simpa only [one_mul] using Nat.mul_le_mul_right X hW)
  have hc := stageCost_le c register hs inputs outputs a out time (W * X)
    hi ho hdi hdo ha' hout
  have hw := returned_wordBound c register hs inputs outputs a out (W * X)
    hi ho hdi hdo ha' hout
  have hWP : W * X + 1 ≤ (W + 1) * X ^ q := by
    calc
      W * X + 1 ≤ W * X ^ q + X ^ q :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hXP) h1P
      _ = (W + 1) * X ^ q := by ring
  have hcoef : W ≤ coefficient s inputs.length outputs.length W T :=
    le_trans (by omega) (coefficient_ge_width _ _ _ _ _)
  refine ⟨?_, wordBound_mono hw
    (Nat.mul_le_mul hcoef hXP)⟩
  calc
    stageCost c register hs inputs outputs a out time ≤
        time + storageOverhead s inputs.length outputs.length (W * X) := hc
    _ ≤ T * X ^ q +
        (6 * s + 7 * inputs.length + 10 * outputs.length + 21) * (W * X + 1) :=
      Nat.add_le_add ht (storageOverhead_linear _ _ _ _)
    _ ≤ T * X ^ q +
        (6 * s + 7 * inputs.length + 10 * outputs.length + 22) * ((W + 1) * X ^ q) :=
      Nat.add_le_add_left (Nat.mul_le_mul (by omega) hWP) _
    _ = coefficient s inputs.length outputs.length W T * X ^ q := by
      unfold coefficient
      ring

theorem selectM_polynomial (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ (B P : ℕ) (a : SetupState c) (t : ℕ) (b : SetupState c),
      WordBound B a → Eval (selectM c) t a b →
        t ≤ C * (B + P + 1) ^ q ∧ WordBound (C * (B + P + 1) ^ q) b := by
  refine ⟨coefficient 3 1 1 (c.T + 5) (c.T + 27), 2,
    coefficient_pos _ _ _ _ _, by decide, ?_⟩
  intro B P a t b ha he
  let X := B + P + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hBX : B ≤ X := by dsimp [X]; omega
  have hl := ha (persistent c 4)
  have hlenX : (a.stacks (persistent c 4)).length ≤ X := hl.trans hBX
  have hXP : X ≤ X ^ 2 := Nat.le_self_pow (by decide) X
  have hout : WordBound ((c.T + 5) * X)
      (selectOutput c.T (a.stacks (persistent c 4))) := by
    intro i
    by_cases hi : i = 2
    · subst i
      have h := SparsificationBudgetProgram.outputWord_length_le c.T
        (a.stacks (persistent c 4))
      have hlin := linear_le 2 (c.T + 3) _ X hlenX hX
      change (SparsificationBudgetProgram.outputWord c.T
        (CounterPrograms.value (a.stacks (persistent c 4)))).length ≤ _
      apply h.trans
      calc
        c.T + 2 * (a.stacks (persistent c 4)).length + 3 =
            2 * (a.stacks (persistent c 4)).length + (c.T + 3) := by omega
        _ ≤ (2 + (c.T + 3)) * X := hlin
        _ = (c.T + 5) * X := by ring
    · simp [selectOutput, StructuredProgram.ioState, hi]
  have htime : SparsificationBudgetProgram.runtimeBound c.T
      (a.stacks (persistent c 4)).length ≤ (c.T + 27) * X ^ 2 := by
    have hlin := linear_le 10 (c.T + 17) _ X hlenX hX
    have h' : SparsificationBudgetProgram.runtimeBound c.T
        (a.stacks (persistent c 4)).length ≤ (c.T + 27) * X := by
      calc
        _ = 10 * (a.stacks (persistent c 4)).length + (c.T + 17) := by
          unfold SparsificationBudgetProgram.runtimeBound
          omega
        _ ≤ (10 + (c.T + 17)) * X := hlin
        _ = (c.T + 27) * X := by ring
    exact h'.trans (Nat.mul_le_mul_left _ hXP)
  have hb := stage_bound c (registerPort (by decide : 3 ≤ 9))
    (small_fits c (by decide : 3 ≤ 32)) [(persistent c 4, 0)] [(2, persistent c 23)]
    a (selectOutput c.T (a.stacks (persistent c 4))) _ X (c.T + 5) (c.T + 27) 2
    (by simp) (by simp) (by simp) (by simp) hX (by omega) (by decide)
    (wordBound_mono ha hBX) hout htime
  obtain ⟨n, hn, hd, _, _, _⟩ := selectM_eval c a
  exact transfer he hd (hn.trans hb.1) hb.2

private theorem occurrence_word (c : Config) (a : SetupState c)
    (rf : Fin 8 → Bool) (word : List Bool) :
    (occurrenceResult c a rf word).stacks (persistent c 24) = word := by
  exact returned_word c (registerPort (by decide : 8 ≤ 9)) (occurrenceFits c)
    [(persistent c 23, (SparsificationThresholdProgram.occurrenceProgram c.k).inputStack)]
    [((SparsificationThresholdProgram.occurrenceProgram c.k).outputStack, persistent c 24)]
    a (occurrenceOut c a rf word) (by simp) (by simp)
    ((SparsificationThresholdProgram.occurrenceProgram c.k).outputStack, persistent c 24) (by simp)

theorem occurrence_polynomial (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ (B P : ℕ) (a : SetupState c) (t : ℕ) (b : SetupState c),
      WordBound B a → Eval (occurrence c) t a b →
        t ≤ C * (B + P + 1) ^ q ∧ WordBound (C * (B + P + 1) ^ q) b := by
  let e := SparsificationThresholdProgram.occurrenceExpr c.k
  let W := ArithmeticExpressionProgram.widthCoeff e + 1
  let T := ArithmeticExpressionProgram.timeCoeff e + 1
  refine ⟨coefficient (ArithmeticExpressionProgram.slots e) 1 1 W T, 2,
    coefficient_pos _ _ _ _ _, by decide, ?_⟩
  intro B P a t b ha he
  let X := B + P + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hBX : B ≤ X := by dsimp [X]; omega
  have hW : 1 ≤ W := by dsimp [W]; omega
  have hl := ha (persistent c 23)
  have hlen : (a.stacks (persistent c 23)).length + 1 ≤ X := by dsimp [X]; omega
  obtain ⟨n, rf, word, hn, hd, _, hw, _⟩ := occurrence_eval c a
  rw [occurrence_word] at hw
  have hw' : word.length ≤ W * X := hw.trans
    (Nat.mul_le_mul (by dsimp [W, e]; omega) hlen)
  have hin : (a.stacks (persistent c 23)).length ≤ W * X :=
    hl.trans (hBX.trans (by simpa only [one_mul] using Nat.mul_le_mul_right X hW))
  have hout : WordBound (W * X) (occurrenceOut c a rf word) := by
    intro i
    simp only [occurrenceOut, ArithmeticExpressionProgram.state, Function.update_apply]
    split_ifs <;> first | exact hw' | exact hin | exact Nat.zero_le _
  have htime : T * ((a.stacks (persistent c 23)).length + 1) ^ 2 ≤ T * X ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen _)
  have hb := stage_bound c (registerPort (by decide : 8 ≤ 9)) (occurrenceFits c)
    [(persistent c 23, (SparsificationThresholdProgram.occurrenceProgram c.k).inputStack)]
    [((SparsificationThresholdProgram.occurrenceProgram c.k).outputStack, persistent c 24)]
    a (occurrenceOut c a rf word) _ X W T 2
    (by simp) (by simp) (by simp) (by simp) hX hW (by decide)
    (wordBound_mono ha hBX) hout htime
  exact transfer he hd (hn.trans hb.1) hb.2

private theorem incidence_word (c : Config) (a : SetupState c)
    (rf : Fin 8 → Bool) (word : List Bool) :
    (incidenceResult c a rf word).stacks (persistent c 16) = word := by
  exact returned_word c (registerPort (by decide : 8 ≤ 9))
    (small_fits c (by decide : 10 ≤ 32)) [(persistent c 5, 0), (persistent c 24, 1)]
    [(2, persistent c 16)] a (incidenceOut c a rf word) (by simp) (by simp)
    (2, persistent c 16) (by simp)

theorem incidence_polynomial (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ (B P : ℕ) (a : SetupState c) (t : ℕ) (b : SetupState c),
      WordBound B a → Eval (incidence c) t a b →
        t ≤ C * (B + P + 1) ^ q ∧ WordBound (C * (B + P + 1) ^ q) b := by
  refine ⟨coefficient 10 2 1 5 7501, 2, coefficient_pos _ _ _ _ _, by decide, ?_⟩
  intro B P a t b ha he
  let X := B + P + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hBX : B ≤ X := by dsimp [X]; omega
  have h1 := ha (persistent c 5)
  have h2 := ha (persistent c 24)
  have hlen : (a.stacks (persistent c 5)).length +
      (a.stacks (persistent c 24)).length + 3 ≤ 5 * X := by dsimp [X]; omega
  obtain ⟨n, rf, word, hn, hd, _, hw, _⟩ := incidence_eval c a
  rw [incidence_word] at hw
  have hw' : word.length ≤ 5 * X := hw.trans hlen
  have hin1 : (a.stacks (persistent c 5)).length ≤ 5 * X := by omega
  have hin2 : (a.stacks (persistent c 24)).length ≤ 5 * X := by omega
  have hout : WordBound (5 * X) (incidenceOut c a rf word) := by
    intro i
    fin_cases i <;> simp [incidenceOut, incidenceInput, hw', hin1, hin2]
  have hXP : 1 ≤ X ^ 2 := hX.trans (Nat.le_self_pow (by decide) X)
  have htime : 300 * ((a.stacks (persistent c 5)).length +
      (a.stacks (persistent c 24)).length + 3) ^ 2 + 1 ≤ 7501 * X ^ 2 := by
    have h := Nat.mul_le_mul_left 300 (Nat.pow_le_pow_left hlen 2)
    calc
      _ ≤ 300 * (5 * X) ^ 2 + X ^ 2 := Nat.add_le_add h hXP
      _ = 7501 * X ^ 2 := by ring
  have hb := stage_bound c (registerPort (by decide : 8 ≤ 9))
    (small_fits c (by decide : 10 ≤ 32)) [(persistent c 5, 0), (persistent c 24, 1)]
    [(2, persistent c 16)] a (incidenceOut c a rf word) _ X 5 7501 2
    (by simp) (by simp) (by simp) (by simp) hX (by decide) (by decide)
    (wordBound_mono ha hBX) hout htime
  exact transfer he hd (hn.trans hb.1) hb.2

theorem prime_polynomial (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ (B P : ℕ) (a : SetupState c) (t : ℕ) (b : SetupState c),
      WordBound B a → 2 ^ BinaryArithmetic.toNat (a.stacks (persistent c 5)) ≤ P →
      Eval (prime c) t a b →
        t ≤ C * (B + P + 1) ^ q ∧ WordBound (C * (B + P + 1) ^ q) b := by
  refine ⟨coefficient 12 1 1 9 62500000001, 4,
    coefficient_pos _ _ _ _ _, by decide, ?_⟩
  intro B P a t b ha hP he
  let X := B + P + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hBX : B ≤ X := by dsimp [X]; omega
  have hl := ha (persistent c 5)
  have hu : BinaryArithmetic.toNat (a.stacks (persistent c 5)) ≤ 2 ^ BinaryArithmetic.toNat (a.stacks (persistent c 5)) :=
    Nat.le_of_lt Nat.lt_two_pow_self
  have hwidth : SubexpPrimeSelectRuntime.selectorWordBound (a.stacks (persistent c 5)) ≤ 9 * X := by
    rw [SubexpPrimeSelectRuntime.selectorWordBound_eq]
    simp only [SubexpPrimeSelectRuntime.endpointWordBound, SubexpParameterProgram.value_eq_toNat]
    dsimp [X]
    omega
  obtain ⟨n, out, hn, hd, _, _, hw, _⟩ := prime_eval c a
  have hout : WordBound (9 * X) out := fun i => (hw i).trans hwidth
  have htime : SubexpPrimeSelectRuntime.selectorBound (a.stacks (persistent c 5)) + 1 ≤
      62500000001 * X ^ 4 := by
    have hs := SubexpPrimeSelectRuntime.selectorBound_le (a.stacks (persistent c 5))
    simp only [SubexpParameterProgram.value_eq_toNat] at hs
    have harg : (a.stacks (persistent c 5)).length +
        2 ^ BinaryArithmetic.toNat (a.stacks (persistent c 5)) + 5 ≤ 5 * X := by dsimp [X]; omega
    have hXP : 1 ≤ X ^ 4 := hX.trans (Nat.le_self_pow (by decide) X)
    calc
      _ ≤ 100000000 * ((a.stacks (persistent c 5)).length +
          2 ^ BinaryArithmetic.toNat (a.stacks (persistent c 5)) + 5) ^ 4 + 1 := Nat.add_le_add_right hs _
      _ ≤ 100000000 * (5 * X) ^ 4 + X ^ 4 :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left harg _)) hXP
      _ = 62500000001 * X ^ 4 := by ring
  have hb := stage_bound c (registerPort (by decide : 9 ≤ 9))
    (small_fits c (by decide : 12 ≤ 32)) [(persistent c 5, 0)] [(9, persistent c 6)]
    a out _ X 9 62500000001 4 (by simp) (by simp) (by simp) (by simp)
    hX (by decide) (by decide) (wordBound_mono ha hBX) hout htime
  exact transfer he hd (hn.trans hb.1) hb.2

theorem field_polynomial (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ (B P : ℕ) (a : SetupState c) (t : ℕ) (b : SetupState c),
      WordBound B a → 0 < BinaryArithmetic.toNat (a.stacks (persistent c 6)) →
      0 < BinaryArithmetic.toNat (a.stacks (persistent c 16)) → Eval (field c) t a b →
        t ≤ C * (B + P + 1) ^ q ∧ WordBound (C * (B + P + 1) ^ q) b := by
  let D := (8 * c.k).bits.length + 3
  refine ⟨coefficient 16 2 2 (4 * D) (30000 * D ^ 2), 2,
    coefficient_pos _ _ _ _ _, by decide, ?_⟩
  intro B P a t b ha hp hdelta he
  let X := B + P + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hBX : B ≤ X := by dsimp [X]; omega
  have h1 := ha (persistent c 6)
  have h2 := ha (persistent c 16)
  have hwidth : SubexpFieldParameterProgram.width c.k
      (a.stacks (persistent c 6)) (a.stacks (persistent c 16)) ≤ D * X := by
    have hlin := linear_le 2 ((8 * c.k).bits.length + 1) B X hBX hX
    have hlin' : 2 * B + (8 * c.k).bits.length + 1 ≤ D * X := by
      calc
        _ = 2 * B + ((8 * c.k).bits.length + 1) := by omega
        _ ≤ (2 + ((8 * c.k).bits.length + 1)) * X := hlin
        _ = D * X := by dsimp [D]; ring
    exact (show SubexpFieldParameterProgram.width c.k
      (a.stacks (persistent c 6)) (a.stacks (persistent c 16)) ≤
        2 * B + (8 * c.k).bits.length + 1 by
          unfold SubexpFieldParameterProgram.width
          omega).trans hlin'
  obtain ⟨n, out, hn, hd, _, _, _, _, hw, _⟩ := field_eval c a hp hdelta
  have hout : WordBound ((4 * D) * X) out := by
    intro i
    exact (hw i).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 4 hwidth)
  have htime : 30000 * (SubexpFieldParameterProgram.width c.k
      (a.stacks (persistent c 6)) (a.stacks (persistent c 16))) ^ 2 ≤
        (30000 * D ^ 2) * X ^ 2 := by
    calc
      _ ≤ 30000 * (D * X) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hwidth _)
      _ = (30000 * D ^ 2) * X ^ 2 := by ring
  have hnodup : ([persistent c 17, persistent c 25] : List (Fin (stackCount c))).Nodup := by
    simp [persistent, Fin.ext_iff]
  have hb := stage_bound c (registerPort (by decide : 8 ≤ 9))
    (small_fits c (by decide : 16 ≤ 32))
    [(persistent c 6, 0), (persistent c 16, 1)] [(4, persistent c 17), (7, persistent c 25)]
    a out _ X (4 * D) (30000 * D ^ 2) 2 (by simp) (by simp) (by simp) hnodup
    hX (by dsimp [D]; omega) (by decide) (wordBound_mono ha hBX) hout htime
  exact transfer he hd (hn.trans hb.1) hb.2

end SubexponentialSAT.SubexpSetupArithmeticBounds

end OAI.Algorithms
