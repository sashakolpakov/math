import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgramSemantics

namespace OAI.Algorithms

/-! Closed polynomial cost and dimension bound for the complete prefix.
The bound is polynomial in encoded scope length, numeric ambient n and t,
and the lengths of their binary input words; it does not assume precomputed
statistics or claim polynomiality solely in the binary lengths of n,t. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def capacity (scopes : List (List ℕ)) (n t : List Bool) :=
  (scopeBits scopes).length + mass scopes + scopes.length + BinaryArithmetic.toNat n + BinaryArithmetic.toNat t +
    n.length + t.length + 2

theorem mass_le_input (scopes : List (List ℕ)) : mass scopes ≤ (scopeBits scopes).length := by
  induction scopes with
  | nil => simp [mass, scopeBits, SubexpIncidenceSlotProgram.scopeBits, Encoding.encodeList]
  | cons xs xss ih =>
      have hx := Encoding.length_encodeList_lower Encoding.encodeNat xs
      simp only [mass, List.map_cons, List.sum_cons] at *
      change xs.length + (xss.map List.length).sum ≤
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) (xs :: xss)).length
      rw [Encoding.length_encodeList_cons]
      change (xss.map List.length).sum ≤
        (Encoding.encodeList (Encoding.encodeList Encoding.encodeNat) xss).length at ih
      omega

theorem count_le_input (scopes : List (List ℕ)) : scopes.length ≤ (scopeBits scopes).length := by
  exact (Nat.le_succ _).trans (Encoding.length_encodeList_lower _ _)

def inputCapacity (scopes : List (List ℕ)) (n t : List Bool) :=
  (scopeBits scopes).length + BinaryArithmetic.toNat n + BinaryArithmetic.toNat t + n.length + t.length + 2

theorem capacity_le_input (scopes : List (List ℕ)) (n t : List Bool) :
    capacity scopes n t ≤ 3 * inputCapacity scopes n t := by
  have := mass_le_input scopes
  have := count_le_input scopes
  dsimp [capacity, inputCapacity]
  omega

theorem cut_le_product (scopes : List (List ℕ)) (n t : List Bool) (hn : 0 < BinaryArithmetic.toNat n) :
    cut scopes n t ≤ mass scopes * BinaryArithmetic.toNat t := by
  apply (ceilDiv_le_iff_le_mul hn).mpr
  have h := Nat.le_mul_of_pos_left (mass scopes * BinaryArithmetic.toNat t) hn
  simpa [Nat.mul_comm] using h

theorem unarySized_le (value size R : ℕ) (hR : 2 ≤ R) (hv : value ≤ R^2) (hs : size ≤ R) :
    unarySized value size ≤ 100 * R^3 := by
  have h := Nat.mul_le_mul (Nat.add_le_add_right hv 1) (Nat.add_le_add_right hs 1)
  have hsq : 2 * R ≤ R^2 := by nlinarith only [hR]
  have hcube : 2 * R^2 ≤ R^3 := by nlinarith only [Nat.mul_le_mul_left (R^2) hR]
  dsimp [unarySized]
  nlinarith only [h, hR, hsq, hcube]

theorem budget_le (scopes : List (List ℕ)) (n t : List Bool) (hn : 0 < BinaryArithmetic.toNat n) :
    budget scopes n t + 1 ≤ 10000 * (capacity scopes n t)^3 := by
  let R := capacity scopes n t
  have hR : 2 ≤ R := by dsimp [R, capacity]; omega
  have hs : mass scopes ≤ R := by dsimp [R, capacity]; omega
  have he : scopes.length ≤ R := by dsimp [R, capacity]; omega
  have hnR : BinaryArithmetic.toNat n ≤ R := by dsimp [R, capacity]; omega
  have htR : BinaryArithmetic.toNat t ≤ R := by dsimp [R, capacity]; omega
  have hsum : (scopeBits scopes).length + scopes.length + BinaryArithmetic.toNat n + 1 ≤ R := by dsimp [R, capacity]; omega
  have hsize : mass scopes + t.length + n.length + 2 ≤ R := by dsimp [R, capacity]; omega
  have hinput : (scopeBits scopes).length + 1 ≤ R := by dsimp [R, capacity]; omega
  have hq : cut scopes n t ≤ R^2 := (cut_le_product scopes n t hn).trans (by
    simpa [pow_two] using Nat.mul_le_mul hs htR)
  have hsq : R ≤ R^2 := by nlinarith only [hR]
  have hcube : R^2 ≤ R^3 := by nlinarith only [Nat.mul_le_mul_left (R^2) hR]
  have hcount : SubexpScopeCountSetup.countBudget (records scopes) + 1 ≤ 14 * R := by
    have hc := SubexpSunflowerProgram.CountRecords.steps_le_encoded (records scopes)
    rw [records_bits] at hc
    dsimp [SubexpScopeCountSetup.countBudget, SubexpSunflowerProgram.CountRecords.steps]
    rw [records_bits]
    dsimp [SubexpSunflowerProgram.CountRecords.steps] at hc
    omega
  have hmass : MassPreserve.bound (scopeBits scopes) ≤ 40 * R := by
    dsimp [MassPreserve.bound]; omega
  have hbin : SubexpFactorCountSetup.countBudget (mass scopes) + 1 ≤ 30 * R^2 := by
    have hs2 := Nat.mul_self_le_mul_self hs
    dsimp [SubexpFactorCountSetup.countBudget]
    nlinarith only [hs2, hs, hsq, hR]
  have hcut : Cutoff.bound (List.replicate (mass scopes) false) t n ≤ 601 * R^2 := by
    have ha : mass scopes + t.length + 1 ≤ R := by omega
    have hb := Nat.pow_le_pow_left hsize 2
    have hc := Nat.pow_le_pow_left ha 2
    dsimp [Cutoff.bound]
    simp only [List.length_replicate]
    nlinarith only [hb, hc, hR]
  have hu : unarySized (cut scopes n t) (mass scopes + t.length + 2) ≤ 100 * R^3 :=
    unarySized_le _ _ _ hR hq (by omega)
  have hf : unarySized (BinaryArithmetic.toNat n) n.length ≤ 100 * R^3 :=
    unarySized_le _ _ _ hR (hnR.trans hsq) (by omega)
  have hquery : uniformQueryBudget scopes (BinaryArithmetic.toNat n) (cut scopes n t) + 2 ≤ 1100 * R^2 := by
    have hb := Nat.pow_le_pow_left hsum 2
    dsimp [uniformQueryBudget]
    nlinarith only [hb, hq, he, hsq, hR]
  have hscan : scanBudget scopes (BinaryArithmetic.toNat n) (cut scopes n t) + 1 ≤ 1100 * R^3 + 3 := by
    apply (scanBudget_le scopes (BinaryArithmetic.toNat n) (cut scopes n t)).trans
    have h := Nat.mul_le_mul hnR hquery
    nlinarith only [h]
  dsimp [budget]
  nlinarith only [hcount, hmass, hbin, hcut, hu, hf, hscan, hsq, hcube, hR]

theorem mask_dimension (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (n t : List Bool) (hn : 0 < BinaryArithmetic.toNat n) (ht : 0 < BinaryArithmetic.toNat t) :
    ∃ b : Data, RunsIn program (10000 * (capacity scopes n t)^3)
      ((initial regs scopes n t).withPC (some program.entry)) (b.withPC none) ∧
      (b.stacks 14).length = BinaryArithmetic.toNat n ∧ Branches.trueCount (b.stacks 14) ≤ BinaryArithmetic.toNat n / BinaryArithmetic.toNat t := by
  obtain ⟨b, hr, hm⟩ := runsIn regs scopes n t hn
  refine ⟨b, hr.mono (budget_le scopes n t hn), ?_, ?_⟩
  · rw [hm]; exact highPrefix_length _ _ _
  · rw [hm]
    exact computed_high_dimension_rawMass scopes (BinaryArithmetic.toNat n) (BinaryArithmetic.toNat t) hn ht

theorem input_budget (scopes : List (List ℕ)) (n t : List Bool) (hn : 0 < BinaryArithmetic.toNat n) :
    budget scopes n t + 1 ≤ 270000 * (inputCapacity scopes n t)^3 := by
  apply (budget_le scopes n t hn).trans
  have h := Nat.pow_le_pow_left (capacity_le_input scopes n t) 3
  nlinarith

theorem primitive_run (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (n t : List Bool) (hn : 0 < BinaryArithmetic.toNat n) :
    ∃ b : Data, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (270000 * (inputCapacity scopes n t)^3))
      (primitiveCfg program ((initial regs scopes n t).withPC (some program.entry)))
      (primitiveCfg program (b.withPC none)) ∧
      b.stacks 14 = highPrefix scopes (cut scopes n t) (BinaryArithmetic.toNat n) := by
  obtain ⟨b, hr, hm⟩ := runsIn regs scopes n t hn
  exact ⟨b, BitProgram.primitive_execution program (hr.mono (input_budget scopes n t hn)), hm⟩

theorem remaining_at_least_half (scopes : List (List ℕ)) (n t : List Bool)
    (hn : 0 < BinaryArithmetic.toNat n) (ht : 2 ≤ BinaryArithmetic.toNat t) :
    BinaryArithmetic.toNat n / 2 ≤ BinaryArithmetic.toNat n - Branches.trueCount (highPrefix scopes (cut scopes n t) (BinaryArithmetic.toNat n)) := by
  have hp : 0 < BinaryArithmetic.toNat t := by omega
  have hh := computed_high_dimension_rawMass scopes (BinaryArithmetic.toNat n) (BinaryArithmetic.toNat t) hn hp
  change Branches.trueCount (highPrefix scopes (cut scopes n t) (BinaryArithmetic.toNat n)) ≤ BinaryArithmetic.toNat n / BinaryArithmetic.toNat t at hh
  have hm := (Nat.le_div_iff_mul_le hp).mp hh
  have htwo := Nat.mul_le_mul_left
    (Branches.trueCount (highPrefix scopes (cut scopes n t) (BinaryArithmetic.toNat n))) ht
  omega

theorem ambient_le_twice_remaining (scopes : List (List ℕ)) (n t : List Bool)
    (hn : 0 < BinaryArithmetic.toNat n) (ht : 2 ≤ BinaryArithmetic.toNat t) :
    BinaryArithmetic.toNat n ≤ 2 * (BinaryArithmetic.toNat n - Branches.trueCount (highPrefix scopes (cut scopes n t) (BinaryArithmetic.toNat n))) := by
  have hp : 0 < BinaryArithmetic.toNat t := by omega
  have hh := computed_high_dimension_rawMass scopes (BinaryArithmetic.toNat n) (BinaryArithmetic.toNat t) hn hp
  change Branches.trueCount (highPrefix scopes (cut scopes n t) (BinaryArithmetic.toNat n)) ≤ BinaryArithmetic.toNat n / BinaryArithmetic.toNat t at hh
  have hm := (Nat.le_div_iff_mul_le hp).mp hh
  have htwo := Nat.mul_le_mul_left
    (Branches.trueCount (highPrefix scopes (cut scopes n t) (BinaryArithmetic.toNat n))) ht
  omega

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
