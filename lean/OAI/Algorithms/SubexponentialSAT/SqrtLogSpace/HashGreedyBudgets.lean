import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionHashBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyUniform
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyStagedSpace

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyBudgets
open SqrtLog HashGreedyProgram

/-- The explicit old controller pays every scored candidate, independently of
whether the candidate wins. -/
theorem controller_lower (B C cost familyBits count rounds : ℕ) :
    rounds * count * (cost + B + C + 1) ≤
      HashSelectProgram.controllerBudget B C cost familyBits count rounds := by
  unfold HashSelectProgram.controllerBudget HashSelectProgram.roundsBudget
    HashSelectProgram.roundBudget HashSelectProgram.selectBudget HashSelectProgram.loadBudget
  nlinarith only [Nat.zero_le (rounds * familyBits), Nat.zero_le (rounds * count * cost),
    Nat.zero_le (rounds * count * B), Nat.zero_le (rounds * count * C)]

/-- All actual seed and streamed candidate attempts are paid. The retained
payload count can be exponentially large, but appears only in time. -/
theorem rounds_le_square (attempt B C oldCost oldWidth familyBits count rounds factor : ℕ)
    (hcount : 1 ≤ count) (hfamily : 2 ^ C ≤ count ^ 2)
    (hC : C ≤ oldWidth)
    (hattempt : attempt ≤ factor * (oldCost + B + oldWidth + 1)) :
    HashSelectProgram.roundsBudget (NativeRound.roundBudget attempt B C) rounds ≤
      402 * (factor + 1) * count *
        (HashSelectProgram.controllerBudget B oldWidth oldCost familyBits count rounds + 1) := by
  let X := oldCost + B + oldWidth + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hsum : attempt + B + C + 1 ≤ (factor + 1) * X := by
    dsimp [X] at *
    nlinarith only [hattempt, hC, Nat.zero_le oldCost]
  have hround := (NativeRound.round_budget_le attempt B C).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 400 hfamily) hsum)
  have hlower := controller_lower B oldWidth oldCost familyBits count rounds
  change rounds * count * X ≤ _ at hlower
  have hprod := Nat.mul_le_mul_left (400 * (factor + 1) * count) hlower
  have hr := Nat.mul_le_mul_left rounds hround
  have hrounds : rounds ≤ rounds * count * X := by
    have h := Nat.mul_le_mul hcount hX
    nlinarith only [Nat.mul_le_mul_left rounds h]
  unfold HashSelectProgram.roundsBudget
  nlinarith only [hprod, hr, hrounds, hcount,
    Nat.mul_le_mul_left (rounds * count * X) (show 1 ≤ factor + 1 by omega),
    Nat.mul_le_mul_left (rounds * count * X) hcount,
    Nat.zero_le (factor * count)]

/-- Paid preparation, every marked query, and full score padding have a fixed
polynomial overhead in retained parameters and the uniform query cost. -/
theorem attempt_polynomial (a : HashMassAdapter.Data) (queryCost width : List Bool → ℕ)
    (m depth W D T B : ℕ) (hm : CounterPrograms.value (a.stacks 782) = m)
    (h0 : (a.stacks 0).length ≤ D) (h782 : (a.stacks 782).length ≤ D)
    (h769 : (a.stacks 769).length ≤ D)
    (hw : ∀ e : Fin m, width (Encoding.encodeNat e.val) ≤ W)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    15 * HashCandidateProgram.Leaf.budget m depth +
      HashMassAdapter.massBudget a queryCost width m + 23 * B + 20 ≤
        2000000 * (m + depth + W + D + B + 1) ^ 3 * (T + 1) := by
  let S := m + depth + W + D + B + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hd : depth + 1 ≤ S := by dsimp [S]; omega
  have hmS : m + 1 ≤ S := by dsimp [S]; omega
  have hBS : B ≤ S := by dsimp [S]; omega
  have hmass := HashMassBounds.massBudget_le a queryCost width m W D T hm h0 h782 h769 hw ht
  have hmassS : HashMassAdapter.massBudget a queryCost width m ≤ 1000 * S ^ 3 * (T + 1) :=
    hmass.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left (by dsimp [S]; omega) 3)))
  have hwidth : HashCandidates.digitWidth m + 1 ≤ 3 * S := by
    have h := DyadicWidth.width_le_succ (3 * m)
    change HashCandidates.digitWidth m ≤ 3 * m + 1 at h
    omega
  have hprep := HashCandidateProgram.Leaf.budget_polynomial m depth
  have hprepS : HashCandidateProgram.Leaf.budget m depth ≤ 55800 * S ^ 3 := by
    have hp := Nat.mul_le_mul (Nat.mul_le_mul_left 6200 hd)
      (Nat.pow_le_pow_left hwidth 2)
    nlinarith only [hprep, hp]
  have hS3 : S ≤ S ^ 3 := (Nat.le_self_pow (by omega) S).trans
    (Nat.pow_le_pow_right hS (show 2 ≤ 3 by omega))
  have hST : S ^ 3 ≤ S ^ 3 * (T + 1) := Nat.le_mul_of_pos_right _ (by omega)
  change _ ≤ 2000000 * S ^ 3 * (T + 1)
  nlinarith only [hmassS, hprepS, hBS, hS, hS3, hST]


/-- The named actual attempt includes the all-mark mass collector and the
common-width score padding after the native normalizer. -/
theorem attemptBudget_polynomial (a : HashMassAdapter.Data) (queryCost : List Bool → ℕ)
    (n m depth D T : ℕ) (hm : CounterPrograms.value (a.stacks 782) = m)
    (h0 : (a.stacks 0).length ≤ D) (h782 : (a.stacks 782).length ≤ D)
    (h769 : (a.stacks 769).length ≤ D)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    HashGreedyExecution.attemptBudget a n m depth queryCost ≤
      2000000 * (m + depth + (n + 1) + D + HashSelect.loopCap n m + 1) ^ 3 * (T + 1) := by
  have h := attempt_polynomial a queryCost (fun _ => n + 1) m depth (n + 1) D T
    (HashSelect.loopCap n m) hm h0 h782 h769 (fun _ => le_rfl) ht
  unfold HashGreedyExecution.attemptBudget
  omega

/-- The old explicit family-generation term alone dominates the square of
its original ternary candidate count. -/
theorem family_square_le_polynomial (count depth rounds : List Bool) (B C cost : ℕ)
    (hc : 2 ≤ CounterPrograms.value count) :
    (CounterPrograms.value count ^ CounterPrograms.value depth) ^ 2 ≤
      Execution.Hash.polynomialBudget count depth rounds B C cost := by
  let A := CounterPrograms.value count
  let P := CounterPrograms.value depth
  let M := A ^ P
  have hcoef : 1 ≤ 400 * (P + 1) * A ^ 2 * ((P + 1) * count.length + 1) := by
    have hA : 1 ≤ A := by dsimp [A]; omega
    have hApos : 0 < A := by omega
    have hp : 0 < 400 * (P + 1) * A ^ 2 * ((P + 1) * count.length + 1) := by positivity
    omega
  have hprod := Nat.mul_le_mul_right (M ^ 2) hcoef
  change M ^ 2 ≤ _
  unfold Execution.Hash.polynomialBudget
  change M ^ 2 ≤ _ + 400 * (P + 1) * A ^ 2 * M ^ 2 * ((P + 1) * count.length + 1) + 15 + _
  nlinarith only [hprod]

/-- Replacing materialized candidates by the complete binary stream costs a
fixed square of the old worst-case budget. No successful-run time is used. -/
theorem rounds_le_polynomial (count depth rounds : List Bool)
    (m B cost attempt factor : ℕ) (hm : 0 < m)
    (hcount : CounterPrograms.value count = 3 * m)
    (hattempt : attempt ≤ factor * (cost + B + CounterPrograms.value depth * count.length + 1)) :
    HashSelectProgram.roundsBudget
      (NativeRound.roundBudget attempt B
        (HashCandidates.payloadWidth m (CounterPrograms.value depth)))
      (CounterPrograms.value rounds) ≤
        402 * (factor + 1) *
          (Execution.Hash.polynomialBudget count depth rounds B
            (CounterPrograms.value depth * count.length) cost + 1) ^ 2 := by
  let P := CounterPrograms.value depth
  let M := CounterPrograms.value count ^ P
  let E := Execution.Hash.polynomialBudget count depth rounds B (P * count.length) cost
  have hcount' : 2 ≤ CounterPrograms.value count := by omega
  have hM : 1 ≤ M := Nat.one_le_pow _ _ (by omega)
  have hM2 : M ^ 2 ≤ E := family_square_le_polynomial count depth rounds B _ cost hcount'
  have hME : M ≤ E := (show M ≤ M ^ 2 by nlinarith only [hM]).trans hM2
  have hcwidth := HashGreedyCandidate.digitWidth_le_word_length hm count hcount
  have hwidth : HashCandidates.payloadWidth m P ≤ P * count.length :=
    Nat.mul_le_mul_left P hcwidth
  have hfamily : 2 ^ HashCandidates.payloadWidth m P ≤ M ^ 2 := by
    simpa only [M, hcount] using HashCandidates.candidate_count_le_square hm P
  have hcontrol : HashSelectProgram.controllerBudget B (P * count.length) cost
      (1 + (2 * (P * count.length) + 2) * M) M (CounterPrograms.value rounds) ≤ E := by
    dsimp [E, Execution.Hash.polynomialBudget, M, P]
    omega
  have h := rounds_le_square attempt B (HashCandidates.payloadWidth m P) cost
    (P * count.length) (1 + (2 * (P * count.length) + 2) * M) M
    (CounterPrograms.value rounds) factor hM hfamily hwidth hattempt
  have hprod : M * (HashSelectProgram.controllerBudget B (P * count.length) cost
      (1 + (2 * (P * count.length) + 2) * M) M (CounterPrograms.value rounds) + 1) ≤
      (E + 1) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (hME.trans (Nat.le_succ E))
      (Nat.add_le_add_right hcontrol 1)
  exact h.trans (by simpa only [Nat.mul_assoc] using
    Nat.mul_le_mul_left (402 * (factor + 1)) hprod)


/-- Complete actual attempts, including all marked queries and padding,
fit a fixed fifth power of the old explicit controller budget and input
parameters. The power is independent of every runtime input. -/
theorem actual_rounds_le_fifth_power (a : HashMassAdapter.Data)
    (count depth rounds : List Bool) (queryCost : List Bool → ℕ)
    (n m D T : ℕ) (hm : 0 < m)
    (hcount : CounterPrograms.value count = 3 * m)
    (hmword : CounterPrograms.value (a.stacks 782) = m)
    (h0 : (a.stacks 0).length ≤ D) (h782 : (a.stacks 782).length ≤ D)
    (h769 : (a.stacks 769).length ≤ D)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    let P := CounterPrograms.value depth
    let B := HashSelect.loopCap n m
    let S := m + P + (n + 1) + D + B + 1
    let E := Execution.Hash.polynomialBudget count depth rounds B (P * count.length) T
    HashSelectProgram.roundsBudget
      (NativeRound.roundBudget (HashGreedyExecution.attemptBudget a n m P queryCost) B
        (HashCandidates.payloadWidth m P)) (CounterPrograms.value rounds) ≤
      1000000000 * (S + E + 1) ^ 5 := by
  intro P B S E
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hattempt := attemptBudget_polynomial a queryCost n m P D T hmword h0 h782 h769 ht
  have hcost : HashGreedyExecution.attemptBudget a n m P queryCost ≤
      (2000000 * S ^ 3) * (T + B + P * count.length + 1) :=
    hattempt.trans (Nat.mul_le_mul_left _ (by omega))
  have hr := rounds_le_polynomial count depth rounds m B T
    (HashGreedyExecution.attemptBudget a n m P queryCost) (2000000 * S ^ 3) hm hcount hcost
  change _ ≤ 402 * (2000000 * S ^ 3 + 1) * (E + 1) ^ 2 at hr
  have hcoef : 2000000 * S ^ 3 + 1 ≤ 2000001 * S ^ 3 := by
    have h1 := Nat.one_le_pow 3 S hS
    omega
  have hp : S ^ 3 * (E + 1) ^ 2 ≤ (S + E + 1) ^ 5 := by
    have h := Nat.mul_le_mul (Nat.pow_le_pow_left (show S ≤ S + E + 1 by omega) 3)
      (Nat.pow_le_pow_left (show E + 1 ≤ S + E + 1 by omega) 2)
    simpa only [← pow_add] using h
  calc
    _ ≤ 402 * (2000000 * S ^ 3 + 1) * (E + 1) ^ 2 := hr
    _ ≤ 402 * (2000001 * S ^ 3) * (E + 1) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcoef)
    _ = 804000402 * (S ^ 3 * (E + 1) ^ 2) := by ring
    _ ≤ 804000402 * (S + E + 1) ^ 5 := Nat.mul_le_mul_left _ hp
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)

/-- A fixed power substitution into a nonnegative linear measured cost stays
a fixed power, including a zero loop coefficient. -/
theorem linear_budget_substitute (base coeff oldCost newCost factor degree : ℕ)
    (hbase : coeff ≤ base) (hnew : newCost ≤ factor * (oldCost + 1) ^ degree) :
    base + coeff * newCost ≤
      (factor + 1) * (base + coeff * oldCost + 1) ^ (degree + 1) := by
  let E := base + coeff * oldCost + 1
  change base + coeff * newCost ≤ (factor + 1) * E ^ (degree + 1)
  have hE : 1 ≤ E := by dsimp [E]; omega
  have hbE : base ≤ E := by dsimp [E]; omega
  have hcE : coeff ≤ E := hbase.trans hbE
  have hp : E ≤ E ^ (degree + 1) := Nat.le_self_pow (by omega) E
  by_cases hc : coeff = 0
  · subst coeff
    simp only [Nat.zero_mul, Nat.add_zero] at *
    nlinarith only [hbE, hp, Nat.zero_le (factor * E ^ (degree + 1))]
  have hcost : oldCost + 1 ≤ E := by
    have h := Nat.mul_le_mul_right oldCost (show 1 ≤ coeff by omega)
    dsimp [E]
    omega
  have hnp : newCost ≤ factor * E ^ degree := hnew.trans
    (Nat.mul_le_mul_left factor (Nat.pow_le_pow_left hcost degree))
  have hterm : coeff * newCost ≤ factor * E ^ (degree + 1) := by
    have h := Nat.mul_le_mul hcE hnp
    simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  nlinarith only [hterm, hbE, hp]



/-- The original explicit hash budget is affine in its paid mass-query cost. -/
theorem polynomialBudget_affine (count depth rounds : List Bool) (B C cost : ℕ) :
    Execution.Hash.polynomialBudget count depth rounds B C cost =
      Execution.Hash.polynomialBudget count depth rounds B C 0 +
        (CounterPrograms.value rounds *
          (CounterPrograms.value count ^ CounterPrograms.value depth + 1)) * cost := by
  unfold Execution.Hash.polynomialBudget HashSelectProgram.controllerBudget
    HashSelectProgram.roundsBudget HashSelectProgram.roundBudget
    HashSelectProgram.selectBudget HashSelectProgram.loadBudget
  ring

/-- A fixed polynomial increase in the per-query measured cost can be charged
inside the original explicit hash budget without an input-dependent power. -/
theorem polynomialBudget_substitute (count depth rounds : List Bool)
    (B C oldCost newCost factor degree : ℕ)
    (hnew : newCost ≤ factor * (oldCost + 1) ^ degree) :
    Execution.Hash.polynomialBudget count depth rounds B C newCost ≤
      (factor + 1) *
        (Execution.Hash.polynomialBudget count depth rounds B C oldCost + 1) ^ (degree + 1) := by
  let coeff := CounterPrograms.value rounds *
    (CounterPrograms.value count ^ CounterPrograms.value depth + 1)
  have hc : coeff ≤ Execution.Hash.polynomialBudget count depth rounds B C 0 := by
    let M := CounterPrograms.value count ^ CounterPrograms.value depth
    let F := 1 + (2 * (CounterPrograms.value depth * count.length) + 2) * M
    have hs : M + 1 ≤ HashSelectProgram.selectBudget B C 0 M := by
      unfold HashSelectProgram.selectBudget
      exact Nat.le_mul_of_pos_right _ (by unfold HashSelectProgram.loadBudget; omega)
    have hr : M + 1 ≤ HashSelectProgram.roundBudget B C 0 F M := by
      unfold HashSelectProgram.roundBudget
      omega
    have hh : coeff ≤ HashSelectProgram.controllerBudget B C 0 F M
        (CounterPrograms.value rounds) := by
      unfold HashSelectProgram.controllerBudget HashSelectProgram.roundsBudget
      change CounterPrograms.value rounds * (M + 1) ≤
        CounterPrograms.value rounds * (HashSelectProgram.roundBudget B C 0 F M + 2) + 2
      exact (Nat.mul_le_mul_left _ (hr.trans (Nat.le_add_right _ 2))).trans
        (Nat.le_add_right _ 2)
    dsimp [Execution.Hash.polynomialBudget]
    exact hh.trans (Nat.le_add_left _ _)
  rw [polynomialBudget_affine count depth rounds B C newCost,
    polynomialBudget_affine count depth rounds B C oldCost]
  exact linear_budget_substitute _ coeff oldCost newCost factor degree hc hnew

/-- A fixed power substitution into a nonnegative linear measured cost stays
a fixed power, including a zero loop coefficient. -/
theorem linear_budget_substitute_with_input (base coeff oldCost newCost factor degree inputLength : ℕ)
    (hbase : coeff ≤ base) (hnew : newCost ≤ factor * (oldCost + inputLength + 1) ^ degree) :
    base + coeff * newCost ≤
      (factor + 1) * (base + coeff * oldCost + inputLength + 1) ^ (degree + 1) := by
  let E := base + coeff * oldCost + inputLength + 1
  change base + coeff * newCost ≤ (factor + 1) * E ^ (degree + 1)
  have hE : 1 ≤ E := by dsimp [E]; omega
  have hbE : base ≤ E := by dsimp [E]; omega
  have hcE : coeff ≤ E := hbase.trans hbE
  have hp : E ≤ E ^ (degree + 1) := Nat.le_self_pow (by omega) E
  by_cases hc : coeff = 0
  · subst coeff
    simp only [Nat.zero_mul, Nat.add_zero] at *
    nlinarith only [hbE, hp, Nat.zero_le (factor * E ^ (degree + 1))]
  have hcost : oldCost + inputLength + 1 ≤ E := by
    have h := Nat.mul_le_mul_right oldCost (show 1 ≤ coeff by omega)
    dsimp [E]
    omega
  have hnp : newCost ≤ factor * E ^ degree := hnew.trans
    (Nat.mul_le_mul_left factor (Nat.pow_le_pow_left hcost degree))
  have hterm : coeff * newCost ≤ factor * E ^ (degree + 1) := by
    have h := Nat.mul_le_mul hcE hnp
    simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  nlinarith only [hterm, hbE, hp]



/-- A fixed polynomial increase in the per-query measured cost can be charged
inside the original explicit hash budget without an input-dependent power. -/
theorem polynomialBudget_substitute_with_input (count depth rounds : List Bool)
    (B C oldCost newCost factor degree inputLength : ℕ)
    (hnew : newCost ≤ factor * (oldCost + inputLength + 1) ^ degree) :
    Execution.Hash.polynomialBudget count depth rounds B C newCost ≤
      (factor + 1) *
        (Execution.Hash.polynomialBudget count depth rounds B C oldCost + inputLength + 1) ^ (degree + 1) := by
  let coeff := CounterPrograms.value rounds *
    (CounterPrograms.value count ^ CounterPrograms.value depth + 1)
  have hc : coeff ≤ Execution.Hash.polynomialBudget count depth rounds B C 0 := by
    let M := CounterPrograms.value count ^ CounterPrograms.value depth
    let F := 1 + (2 * (CounterPrograms.value depth * count.length) + 2) * M
    have hs : M + 1 ≤ HashSelectProgram.selectBudget B C 0 M := by
      unfold HashSelectProgram.selectBudget
      exact Nat.le_mul_of_pos_right _ (by unfold HashSelectProgram.loadBudget; omega)
    have hr : M + 1 ≤ HashSelectProgram.roundBudget B C 0 F M := by
      unfold HashSelectProgram.roundBudget
      omega
    have hh : coeff ≤ HashSelectProgram.controllerBudget B C 0 F M
        (CounterPrograms.value rounds) := by
      unfold HashSelectProgram.controllerBudget HashSelectProgram.roundsBudget
      change CounterPrograms.value rounds * (M + 1) ≤
        CounterPrograms.value rounds * (HashSelectProgram.roundBudget B C 0 F M + 2) + 2
      exact (Nat.mul_le_mul_left _ (hr.trans (Nat.le_add_right _ 2))).trans
        (Nat.le_add_right _ 2)
    dsimp [Execution.Hash.polynomialBudget]
    exact hh.trans (Nat.le_add_left _ _)
  rw [polynomialBudget_affine count depth rounds B C newCost,
    polynomialBudget_affine count depth rounds B C oldCost]
  exact linear_budget_substitute_with_input _ coeff oldCost newCost factor degree inputLength hc hnew

/-- The actual staging and cleanup bound is linear in the retained entry
cap, so it fits the same fixed cube as the normalizer and marked mass. -/
theorem attempt_with_staging_polynomial (a : HashMassAdapter.Data) (queryCost : List Bool → ℕ)
    (n m depth D T : ℕ) (hm : CounterPrograms.value (a.stacks 782) = m)
    (h0 : (a.stacks 0).length ≤ D) (h782 : (a.stacks 782).length ≤ D)
    (h769 : (a.stacks 769).length ≤ D)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    HashGreedyExecution.attemptBudget a n m depth queryCost + 95 * D + 103 ≤
      2100000 * (m + depth + (n + 1) + D + HashSelect.loopCap n m + 1) ^ 3 * (T + 1) := by
  let S := m + depth + (n + 1) + D + HashSelect.loopCap n m + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hD : D ≤ S := by dsimp [S]; omega
  have hpow : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have hmul : S ^ 3 ≤ S ^ 3 * (T + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h := attemptBudget_polynomial a queryCost n m depth D T hm h0 h782 h769 ht
  change _ ≤ 2000000 * S ^ 3 * (T + 1) at h
  change _ ≤ 2100000 * S ^ 3 * (T + 1)
  nlinarith only [h, hS, hD, hpow, hmul]

/-- Paid staging, complete marked mass, padding and final cleanup
fit a fixed fifth power of the old explicit controller budget and input
parameters. The power is independent of every runtime input. -/
theorem staged_rounds_le_fifth_power (a : HashMassAdapter.Data)
    (count depth rounds : List Bool) (queryCost : List Bool → ℕ)
    (n m D T : ℕ) (hm : 0 < m)
    (hcount : CounterPrograms.value count = 3 * m)
    (hmword : CounterPrograms.value (a.stacks 782) = m)
    (h0 : (a.stacks 0).length ≤ D) (h782 : (a.stacks 782).length ≤ D)
    (h769 : (a.stacks 769).length ≤ D)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    let P := CounterPrograms.value depth
    let B := HashSelect.loopCap n m
    let S := m + P + (n + 1) + D + B + 1
    let E := Execution.Hash.polynomialBudget count depth rounds B (P * count.length) T
    HashSelectProgram.roundsBudget
      (NativeRound.roundBudget (HashGreedyExecution.attemptBudget a n m P queryCost + 95 * D + 103) B
        (HashCandidates.payloadWidth m P)) (CounterPrograms.value rounds) ≤
      1000000000 * (S + E + 1) ^ 5 := by
  intro P B S E
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hattempt := attempt_with_staging_polynomial a queryCost n m P D T hmword h0 h782 h769 ht
  have hcost : HashGreedyExecution.attemptBudget a n m P queryCost + 95 * D + 103 ≤
      (2100000 * S ^ 3) * (T + B + P * count.length + 1) :=
    hattempt.trans (Nat.mul_le_mul_left _ (by omega))
  have hr := rounds_le_polynomial count depth rounds m B T
    (HashGreedyExecution.attemptBudget a n m P queryCost + 95 * D + 103) (2100000 * S ^ 3) hm hcount hcost
  change _ ≤ 402 * (2100000 * S ^ 3 + 1) * (E + 1) ^ 2 at hr
  have hcoef : 2100000 * S ^ 3 + 1 ≤ 2100001 * S ^ 3 := by
    have h1 := Nat.one_le_pow 3 S hS
    omega
  have hp : S ^ 3 * (E + 1) ^ 2 ≤ (S + E + 1) ^ 5 := by
    have h := Nat.mul_le_mul (Nat.pow_le_pow_left (show S ≤ S + E + 1 by omega) 3)
      (Nat.pow_le_pow_left (show E + 1 ≤ S + E + 1 by omega) 2)
    simpa only [← pow_add] using h
  calc
    _ ≤ 402 * (2100000 * S ^ 3 + 1) * (E + 1) ^ 2 := hr
    _ ≤ 402 * (2100001 * S ^ 3) * (E + 1) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hcoef)
    _ = 844200402 * (S ^ 3 * (E + 1) ^ 2) := by ring
    _ ≤ 844200402 * (S + E + 1) ^ 5 := Nat.mul_le_mul_left _ hp
    _ ≤ _ := Nat.mul_le_mul_right _ (by decide)


/-- The measured budget belongs to the actual normalize, stage, marked-mass,
cleanup and padding command, not an unstaged query service. -/
theorem named_staged_rounds_le_fifth_power (a : HashMassAdapter.Data)
    (count depth rounds : List Bool) (queryCost : List Bool → ℕ)
    (n m D T : ℕ) (hm : 0 < m)
    (hcount : CounterPrograms.value count = 3 * m)
    (hmword : CounterPrograms.value (a.stacks 782) = m)
    (h0 : (a.stacks 0).length ≤ D) (h782 : (a.stacks 782).length ≤ D)
    (h769 : (a.stacks 769).length ≤ D)
    (ht : ∀ e : Fin m, queryCost (Encoding.encodeNat e.val) ≤ T) :
    let P := CounterPrograms.value depth
    let B := HashSelect.loopCap n m
    let S := m + P + (n + 1) + D + B + 1
    let E := Execution.Hash.polynomialBudget count depth rounds B (P * count.length) T
    HashSelectProgram.roundsBudget
      (NativeRound.roundBudget (HashGreedyExecution.stagedAttemptBudget a n m P queryCost D) B
        (HashCandidates.payloadWidth m P)) (CounterPrograms.value rounds) ≤
      1000000000 * (S + E + 1) ^ 5 := by
  exact staged_rounds_le_fifth_power a count depth rounds queryCost n m D T
    hm hcount hmword h0 h782 h769 ht

/-- The actual staged selector retains polynomial space independently of all
candidate and round counts; only the separately proved query prefix cap appears. -/
theorem staged_rounds_space_le (a : StructuredCalls.State 40 896)
    (n m depth L K : ℕ) (hm : CounterPrograms.value (a.stacks 782) = m)
    (hwords : ∀ i, (a.stacks i).length ≤ L)
    (hrounds : HashSelect.loopCap n m ≤ L)
    (hwidth : HashCandidates.payloadWidth m depth ≤ L) :
    max (HashGreedyStagedSpace.attemptSpace a n m depth L K)
      (896 * L + 100 * (HashSelect.loopCap n m + HashCandidates.payloadWidth m depth + 1) +
        7 * (2 * HashCandidates.payloadWidth m depth + 3) + 20) ≤
      max K (1000000 * (m + depth + L + 1) ^ 3) := by
  let S := m + depth + L + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hL : L ≤ S := by dsimp [S]; omega
  have hpow : S ≤ S ^ 3 := Nat.le_self_pow (by decide) S
  have hbase' := HashMassStagedSpace.spaceBudget_le a m L 0 hm hwords
  simp only [HashMassStagedSpace.spaceBudget, Nat.zero_le, max_eq_right] at hbase'
  have hs : m + L + 1 ≤ S := by dsimp [S]; omega
  have hbaseS := hbase'.trans (Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left hs 3))
  have hprep := HashCandidateProgram.Leaf.budget_polynomial m depth
  have hd : depth + 1 ≤ S := by dsimp [S]; omega
  have hw : HashCandidates.digitWidth m + 1 ≤ 3 * S := by
    have h := DyadicWidth.width_le_succ (3 * m)
    change HashCandidates.digitWidth m ≤ 3 * m + 1 at h
    dsimp [S]
    omega
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_left 6200 hd) (Nat.pow_le_pow_left hw 2)
  have hprepS : HashCandidateProgram.Leaf.budget m depth ≤ 55800 * S ^ 3 := by
    nlinarith only [hprep, hp]
  apply max_le
  · unfold HashGreedyStagedSpace.attemptSpace
    apply max_le (le_max_left _ _) (le_trans ?_ (le_max_right _ _))
    change _ ≤ 1000000 * S ^ 3
    omega
  · apply le_trans _ (le_max_right _ _)
    change _ ≤ 1000000 * S ^ 3
    omega

open SqrtLog.HashSelectProgram

/-- Every old explicit setup/controller term is a fixed polynomial of the
actual retained scalar and word bounds, candidate count, and paid query cost. -/
theorem originalBudget_le_polynomial (count depth rounds : List Bool)
    (B C cost S family : ℕ)
    (ha : CounterPrograms.value count ≤ S) (hp : CounterPrograms.value depth ≤ S)
    (hr : CounterPrograms.value rounds ≤ S)
    (hcw : count.length ≤ S) (hdw : depth.length ≤ S) (hrw : rounds.length ≤ S)
    (hB : B ≤ S) (hC : C ≤ S)
    (hf : CounterPrograms.value count ^ CounterPrograms.value depth ≤ family) :
    Execution.Hash.polynomialBudget count depth rounds B C cost ≤
      10000 * (S + family + cost + 1) ^ 7 := by
  let X := S + family + cost + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hSX : S ≤ X := by dsimp [X]; omega
  have hfX : family ≤ X := by dsimp [X]; omega
  have hcX : cost ≤ X := by dsimp [X]; omega
  have haX := ha.trans hSX
  have hpX := hp.trans hSX
  have hrX := hr.trans hSX
  have hcwX := hcw.trans hSX
  have hdwX := hdw.trans hSX
  have hrwX := hrw.trans hSX
  have hBX := hB.trans hSX
  have hCX := hC.trans hSX
  have hfamily := hf.trans hfX
  have hbound : Execution.Hash.polynomialBudget count depth rounds B C cost ≤
      ((X+1)*(60*X+60)+2*X+3+1+
       (2*X+(X+1)*(16*X+16)+2*X+6+1)+
       (2*X+(X+1)*(16*X+16)+2*X+6+1))+
      400*(X+1)*X^2*X^2*((X+1)*X+1)+15+
      (X*(7*(1+(2*(X*X)+2)*X)+5+
        (X+1)*(6*X+X+10+100*(X+X+1)+4)+5*X+2*X+10+2)+2) := by
    unfold Execution.Hash.polynomialBudget Execution.HashInputs.budget
      Execution.HashAlphabet.budget CounterConversions.coreBound
      controllerBudget roundsBudget roundBudget selectBudget loadBudget
    dsimp only
    gcongr
  apply hbound.trans
  have h2 : X^2 ≤ X^7 := Nat.pow_le_pow_right hX (by decide)
  have h3 : X^3 ≤ X^7 := Nat.pow_le_pow_right hX (by decide)
  have h4 : X^4 ≤ X^7 := Nat.pow_le_pow_right hX (by decide)
  have h5 : X^5 ≤ X^7 := Nat.pow_le_pow_right hX (by decide)
  have h6 : X^6 ≤ X^7 := Nat.pow_le_pow_right hX (by decide)
  have h1 : X ≤ X^7 := Nat.le_self_pow (by decide) X
  have h0 : 1 ≤ X^7 := Nat.one_le_pow _ _ hX
  change _ ≤ 10000*X^7
  nlinarith only [h0,h1,h2,h3,h4,h5,h6]

/-- The candidate factor in the real explicit budget is bounded by the old
all-trial/all-mark call counter, for its exact ternary alphabet and depth. -/
theorem family_le_hashCalls (n m P : ℕ) (hm : 0 < m) :
    (3*m)^P ≤ CostAssembly.hashCalls n m P := by
  have hr : 1 ≤ HashSelect.loopCap n m := by unfold HashSelect.loopCap; omega
  have hprod := Nat.mul_le_mul hr hm
  have hh := Nat.mul_le_mul_left ((3*m)^P) hprod
  have hh' : (3*m)^P ≤ (3*m)^P*HashSelect.loopCap n m*m := by
    simpa only [Nat.succ_eq_add_one, Nat.reduceAdd, Nat.one_mul, Nat.mul_one, Nat.mul_assoc] using hh
  unfold CostAssembly.hashCalls
  apply hh'.trans
  have hdouble := Nat.le_mul_of_pos_left ((3*m)^P*HashSelect.loopCap n m*m)
    (by decide : 0 < 2)
  have heq : 2*((3*m)^P*HashSelect.loopCap n m*m) =
      2*(3*m)^P*HashSelect.loopCap n m*m := by ring
  exact (hdouble.trans_eq heq).trans (Nat.le_succ _)

theorem originalBudget_le_hashCalls (count depth rounds : List Bool)
    (n m P B C cost S : ℕ) (hm : 0 < m)
    (hcount : CounterPrograms.value count = 3*m)
    (hdepth : CounterPrograms.value depth = P)
    (ha : 3*m ≤ S) (hp : P ≤ S) (hr : CounterPrograms.value rounds ≤ S)
    (hcw : count.length ≤ S) (hdw : depth.length ≤ S) (hrw : rounds.length ≤ S)
    (hB : B ≤ S) (hC : C ≤ S) :
    Execution.Hash.polynomialBudget count depth rounds B C cost ≤
      10000 * (S + CostAssembly.hashCalls n m P + cost + 1)^7 := by
  apply originalBudget_le_polynomial count depth rounds B C cost S
    (CostAssembly.hashCalls n m P)
    (hcount ▸ ha) (hdepth ▸ hp) hr hcw hdw hrw hB hC
  simpa only [hcount,hdepth] using family_le_hashCalls n m P hm

/-- The numerical representative of the unary round counter is canonical
binary; its value and length are both charged, without reading the unary
word as a binary number. -/
theorem canonical_originalBudget_le (count depth : List Bool)
    (n m P L cost : ℕ) (hm : 0 < m)
    (hcount : CounterPrograms.value count = 3*m)
    (hdepth : CounterPrograms.value depth = P)
    (hmL : m ≤ L) (hPL : P ≤ L) (hround : HashSelect.loopCap n m ≤ L)
    (hcw : count.length ≤ L) (hdw : depth.length ≤ L) :
    Execution.Hash.polynomialBudget count depth (countWord (HashSelect.loopCap n m))
      (HashSelect.loopCap n m) (P*count.length) cost ≤
      10000*4^7*(L+CostAssembly.hashCalls n m P+cost+1)^14 := by
  let S := 3*(L+1)^2
  have hL : L+1 ≤ S := by dsimp [S]; nlinarith
  have hP : P ≤ S := hPL.trans (by omega)
  have hroundValue : CounterPrograms.value (countWord (HashSelect.loopCap n m)) ≤ S := by
    simp only [CounterPrograms.value_eq_toNat,countWord_toNat]
    omega
  have hword : (countWord (HashSelect.loopCap n m)).length ≤ S := by
    have h := countWord_length_le ((show HashSelect.loopCap n m ≤ 2^(HashSelect.loopCap n m) from Nat.le_of_lt Nat.lt_two_pow_self))
    omega
  have hC : P*count.length ≤ S := by
    have h := Nat.mul_le_mul hPL hcw
    dsimp [S]
    nlinarith only [h, Nat.zero_le L]
  have h := originalBudget_le_hashCalls count depth (countWord (HashSelect.loopCap n m))
    n m P (HashSelect.loopCap n m) (P*count.length) cost S hm hcount hdepth
    (by dsimp [S]; nlinarith only [hmL, Nat.zero_le L]) hP hroundValue
    (hcw.trans (by omega)) (hdw.trans (by omega)) hword (by omega) hC
  let X := L+CostAssembly.hashCalls n m P+cost+1
  have hbase : L+1 ≤ X := by dsimp [X]; omega
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hx : X ≤ X^2 := Nat.le_self_pow (by decide) X
  have hS : S ≤ 3*X^2 := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hbase 2)
  have hsum : S+CostAssembly.hashCalls n m P+cost+1 ≤ 4*X^2 := by
    have hrest : CostAssembly.hashCalls n m P+cost+1 ≤ X := by dsimp [X]; omega
    calc
      _ ≤ 3*X^2+X := by omega
      _ ≤ 4*X^2 := by omega
  apply h.trans
  have hb := Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left hsum 7)
  simpa only [mul_pow,←pow_mul,Nat.mul_assoc] using hb
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyBudgets
