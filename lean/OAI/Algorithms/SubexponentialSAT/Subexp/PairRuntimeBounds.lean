import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreBounds

namespace OAI.Algorithms

/-!
# Uniform bounds for the executed pair scorer

The polynomial parameter bounds physical input lengths.  The exponential
factor is the actual number of tuples emitted by each generator call.
-/

namespace SubexponentialSAT.Subexp.PairRuntimeBounds

open BitProgram PairScoreProgram PairScoreBounds

theorem encoded_length_le (rows : List (List Bool)) (L : ℕ)
    (h : ∀ row ∈ rows, row.length ≤ L) :
    (ProgramEncoding.encodeRecords rows).length ≤ 2 * rows.length * L + 2 * rows.length + 1 := by
  have hv := volume_le rows L h
  rw [ProgramEncoding.encodeRecords_length]
  change 2 * volume rows + 2 * rows.length + 1 ≤ _
  nlinarith

theorem pairRecords_length_le (pairs : List PlanPair) (B : ℕ)
    (h : ∀ pair ∈ pairs, (pairBytes pair).length ≤ B) :
    (pairRecords pairs).length ≤ 2 * pairs.length * B + 2 * pairs.length + 1 := by
  have he := encoded_length_le (pairs.map pairBytes) B (by
    intro bits hbits
    obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hbits
    exact h pair hpair)
  simpa only [List.length_map, pairRecords] using he

theorem volume_member_le (rows : List (List Bool)) (row : List Bool) (h : row ∈ rows) :
    row.length ≤ volume rows := by
  induction rows with
  | nil => simp at h
  | cons head rows ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · exact (ih h).trans (by simp only [volume_cons]; omega)

theorem length_le_encoded (rows : List (List Bool)) :
    rows.length ≤ (ProgramEncoding.encodeRecords rows).length := by
  rw [ProgramEncoding.encodeRecords_length]
  omega

theorem member_length_le_encoded (rows : List (List Bool)) (row : List Bool) (h : row ∈ rows) :
    row.length ≤ (ProgramEncoding.encodeRecords rows).length := by
  have hv := volume_member_le rows row h
  rw [ProgramEncoding.encodeRecords_length]
  change _ ≤ 2 * volume rows + 2 * rows.length + 1
  omega

theorem pair_count_le_encoded (pairs : List PlanPair) : pairs.length ≤ (pairRecords pairs).length := by
  simpa only [List.length_map, pairRecords] using length_le_encoded (pairs.map pairBytes)

theorem pair_length_le_encoded (pairs : List PlanPair) (pair : PlanPair) (h : pair ∈ pairs) :
    (pairBytes pair).length ≤ (pairRecords pairs).length :=
  member_length_le_encoded (pairs.map pairBytes) (pairBytes pair) (List.mem_map.mpr ⟨pair, h, rfl⟩)

theorem powerRows_width (alphabet rows : List (List Bool)) (n L W : ℕ)
    (hr : ∀ row ∈ rows, row.length ≤ L)
    (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    ∀ row ∈ TupleProgram.powerRows alphabet n rows, row.length ≤ L + n * W := by
  induction n generalizing rows L with
  | zero => simpa only [TupleProgram.powerRows, Nat.zero_mul, Nat.add_zero] using hr
  | succ n ih =>
    have h := ih (TupleProgram.cartesianOutput rows alphabet) (L + W)
      (cartesian_width rows alphabet L W hr ha)
    simpa only [TupleProgram.powerRows, Nat.succ_mul, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using h

theorem encoded_generated_length_le (alphabet : List (List Bool)) (n W : ℕ)
    (hA : 1 ≤ alphabet.length) (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    (ProgramEncoding.encodeRecords (TupleProgram.powerRows alphabet n [[]])).length + 1 ≤
      (2 * n * W + 4) * alphabet.length ^ n := by
  have hw := powerRows_width alphabet [[]] n 0 W (by simp) ha
  have hv := volume_le (TupleProgram.powerRows alphabet n [[]]) (n * W) (by simpa using hw)
  rw [TupleProgram.generated_count] at hv
  have hk : 1 ≤ alphabet.length ^ n := one_le_pow₀ hA
  rw [ProgramEncoding.encodeRecords_length, TupleProgram.generated_count]
  change 2 * volume (TupleProgram.powerRows alphabet n [[]]) + 2 * alphabet.length ^ n + 1 + 1 ≤ _
  nlinarith

theorem plan_sizes_le_bytes (plan : List ℕ) :
    plan.sum ≤ (CollisionStreamProgram.planBytes plan).length ∧
      plan.length ≤ (CollisionStreamProgram.planBytes plan).length := by
  have h := GatherProgram.encoded_plan_length plan
  change (CollisionStreamProgram.planBytes plan).length = _ at h
  omega

theorem pair_plan_bytes_le (pair : PlanPair) :
    (CollisionStreamProgram.planBytes pair.1).length ≤ (pairBytes pair).length ∧
      (CollisionStreamProgram.planBytes pair.2).length ≤ (pairBytes pair).length := by
  simp only [pairBytes, List.length_append, Encoding.length_frame]
  omega

theorem fixedCost_le (ctx : Context) (pair : PlanPair) (B : ℕ)
    (hc : ctx.current.flatten.length ≤ B) (hw : ctx.width.length ≤ B)
    (hp : (pairBytes pair).length ≤ B) :
    CollisionTupleProgram.fixedCost ctx.current.flatten ctx.width.length pair.1 pair.2 ≤
      200 * (B + 1) ^ 2 := by
  have hb := pair_plan_bytes_le pair
  have hl := plan_sizes_le_bytes pair.1
  have hr := plan_sizes_le_bytes pair.2
  have hbl := hb.1.trans hp
  have hbr := hb.2.trans hp
  have hsl := hl.1.trans hbl
  have hsr := hr.1.trans hbr
  have hll := hl.2.trans hbl
  have hlr := hr.2.trans hbr
  unfold CollisionTupleProgram.fixedCost CollisionStreamProgram.planBudget
  calc
    _ ≤ 9 * B + 7 * B + 7 * B +
        (34 + (14 * B + 16) * (B + B) + (32 * B + 27) * B + (23 * B + 27) * B) + 21 := by
      gcongr
    _ ≤ 200 * (B + 1) ^ 2 := by nlinarith

theorem generateCost_le (ctx : Context) (pair : PlanPair) (B : ℕ)
    (hA : 1 ≤ ctx.alphabet.length)
    (ha : ∀ row ∈ ctx.alphabet, row.length ≤ ctx.width.length)
    (hc : ctx.current.flatten.length ≤ B) (hw : ctx.width.length ≤ B)
    (hd : ctx.depth.length ≤ B) (hp : (pairBytes pair).length ≤ B) :
    generateCost ctx pair ≤ 4000 * (B + 1) ^ 4 * ctx.alphabet.length ^ ctx.depth.length := by
  let s := B + 1
  let K := ctx.alphabet.length ^ ctx.depth.length
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hk : 1 ≤ K := one_le_pow₀ hA
  have h12 : s ≤ s ^ 2 := le_self_pow₀ hs (by omega)
  have h34 : s ^ 3 ≤ s ^ 4 := pow_le_pow_right₀ hs (by omega)
  have hds : ctx.depth.length + 1 ≤ s := by dsimp [s]; omega
  have hws : ctx.width.length ≤ s := by dsimp [s]; omega
  have hwidth : (ctx.depth.length + 1) * ctx.width.length + 1 ≤ 2 * s ^ 2 := by
    have hmul := Nat.mul_le_mul hds hws
    nlinarith only [hmul, hs]
  have hpow := generated_powerCost_le ctx.alphabet ctx.depth.length ctx.width.length hA ha
  have hpow' : TupleProgram.powerCost ctx.alphabet ctx.depth.length [[]] ≤ 1600 * s ^ 3 * K := by
    calc
      _ ≤ 800 * s * K * (2 * s ^ 2) := hpow.trans (by gcongr)
      _ = _ := by ring
  have hf := fixedCost_le ctx pair B hc hw hp
  have hf' : CollisionTupleProgram.fixedCost ctx.current.flatten ctx.width.length pair.1 pair.2 + 22 ≤
      222 * s ^ 2 := by
    change _ ≤ 222 * (B + 1) ^ 2
    nlinarith only [hf, Nat.zero_le B]
  have he := encoded_generated_length_le ctx.alphabet ctx.depth.length ctx.width.length hA ha
  have he' : (ProgramEncoding.encodeRecords
      (TupleProgram.powerRows ctx.alphabet ctx.depth.length [[]])).length + 1 ≤ 6 * s ^ 2 * K := by
    have hm : ctx.depth.length * ctx.width.length ≤ s ^ 2 := by
      have h := Nat.mul_le_mul (show ctx.depth.length ≤ s by omega) hws
      nlinarith only [h]
    calc
      _ ≤ (2 * ctx.depth.length * ctx.width.length + 4) * K := he
      _ ≤ (6 * s ^ 2) * K := Nat.mul_le_mul_right _ (by nlinarith only [hm, hs])
  have ht := CollisionTupleProgram.sourceBudget_le_serialized ctx.current.flatten
    ctx.width.length pair.1 pair.2 (TupleProgram.powerRows ctx.alphabet ctx.depth.length [[]])
  have ht' : CollisionTupleProgram.sourceBudget ctx.current.flatten ctx.width.length
      pair.1 pair.2 (TupleProgram.powerRows ctx.alphabet ctx.depth.length [[]]) ≤ 1332 * s ^ 4 * K := by
    calc
      _ ≤ (222 * s ^ 2) * (6 * s ^ 2 * K) := ht.trans (Nat.mul_le_mul hf' he')
      _ = _ := by ring
  have hp4 : TupleProgram.powerCost ctx.alphabet ctx.depth.length [[]] ≤ 1600 * s ^ 4 * K :=
    hpow'.trans (by gcongr)
  have h1 : 1 ≤ s ^ 4 * K := Nat.mul_le_mul (one_le_pow₀ hs) hk
  change TupleProgram.powerCost ctx.alphabet ctx.depth.length [[]] +
    CollisionTupleProgram.sourceBudget ctx.current.flatten ctx.width.length pair.1 pair.2
      (TupleProgram.powerRows ctx.alphabet ctx.depth.length [[]]) + 25 ≤ 4000 * s ^ 4 * K
  nlinarith only [h1, hp4, ht']

theorem callbackCost_le (ctx : Context) (pair : PlanPair) (B : ℕ)
    (hA : 1 ≤ ctx.alphabet.length)
    (ha : ∀ row ∈ ctx.alphabet, row.length ≤ ctx.width.length)
    (hc : ctx.current.flatten.length ≤ B) (hw : ctx.width.length ≤ B)
    (hd : ctx.depth.length ≤ B) (hp : (pairBytes pair).length ≤ B) :
    callbackCost ctx (pairBytes pair) ≤ 4100 * (B + 1) ^ 4 * ctx.alphabet.length ^ ctx.depth.length := by
  have hg := generateCost_le ctx pair B hA ha hc hw hd hp
  have hb := pair_plan_bytes_le pair
  have hbl := hb.1.trans hp
  have hbr := hb.2.trans hp
  have hsmall : prepareCost ctx pair + cleanupCost pair ≤ 80 * (B + 1) := by
    unfold prepareCost cleanupCost
    omega
  have hpower : B + 1 ≤ (B + 1) ^ 4 := by
    exact le_self_pow₀ (by omega) (by omega)
  have hk : 1 ≤ ctx.alphabet.length ^ ctx.depth.length := one_le_pow₀ hA
  have hscale : B + 1 ≤ (B + 1) ^ 4 * ctx.alphabet.length ^ ctx.depth.length := by
    simpa using Nat.mul_le_mul hpower hk
  simp only [callbackCost, readPair_pairBytes]
  nlinarith

theorem budget_bounded (cost : List Bool → ℕ) (rows : List (List Bool)) (B C : ℕ)
    (hb : ∀ row ∈ rows, row.length ≤ B) (hc : ∀ row ∈ rows, cost row ≤ C) :
    RecordPrograms.budget cost rows ≤ rows.length * (6 * B + C + 7) := by
  induction rows with
  | nil => simp [RecordPrograms.budget]
  | cons row rows ih =>
    have hr := hb row (by simp)
    have hc' := hc row (by simp)
    have ht := ih (fun x hx => hb x (by simp [hx])) (fun x hx => hc x (by simp [hx]))
    simp only [RecordPrograms.budget, List.length_cons]
    nlinarith

/-- A fixed polynomial in physical input size times the actual per-pair
tuple count.  This bounds the exact source budget of `program_run`. -/
theorem sourceBudget_le (ctx : Context) (pairs : List PlanPair) (B : ℕ)
    (hA : 1 ≤ ctx.alphabet.length)
    (ha : ∀ row ∈ ctx.alphabet, row.length ≤ ctx.width.length)
    (hc : ctx.current.flatten.length ≤ B) (hw : ctx.width.length ≤ B)
    (hd : ctx.depth.length ≤ B) (hn : pairs.length ≤ B)
    (hp : ∀ pair ∈ pairs, (pairBytes pair).length ≤ B) :
    sourceBudget ctx pairs ≤ 5000 * (B + 1) ^ 5 * ctx.alphabet.length ^ ctx.depth.length := by
  let s := B + 1
  let K := ctx.alphabet.length ^ ctx.depth.length
  have hs : 1 ≤ s := by dsimp [s]; omega
  have hk : 1 ≤ K := one_le_pow₀ hA
  have h14 : s ≤ s ^ 4 := le_self_pow₀ hs (by omega)
  have hscale : s ≤ s ^ 4 * K := by simpa using Nat.mul_le_mul h14 hk
  have hb := budget_bounded (callbackCost ctx) (pairs.map pairBytes) B (4100 * s ^ 4 * K)
    (by intro bits h; obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp h; exact hp pair hpair)
    (by intro bits h; obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp h
        exact callbackCost_le ctx pair B hA ha hc hw hd (hp pair hpair))
  rw [List.length_map] at hb
  have hstep : 6 * B + 4100 * s ^ 4 * K + 7 ≤ 4113 * s ^ 4 * K := by
    dsimp [s] at hscale ⊢
    nlinarith
  have hbudget : RecordPrograms.budget (callbackCost ctx) (pairs.map pairBytes) ≤ 4113 * s ^ 5 * K := by
    calc
      _ ≤ pairs.length * (4113 * s ^ 4 * K) := hb.trans (Nat.mul_le_mul_left _ hstep)
      _ ≤ s * (4113 * s ^ 4 * K) := Nat.mul_le_mul_right _ (by dsimp [s]; omega)
      _ = _ := by ring
  have h15 : s ≤ s ^ 5 := le_self_pow₀ hs (by omega)
  have htail : pairs.length * K ≤ s ^ 5 * K := Nat.mul_le_mul_right _ (by dsimp [s] at *; omega)
  have hone : 1 ≤ s ^ 5 * K := Nat.mul_le_mul (one_le_pow₀ hs) hk
  change _ + 5 * (pairs.length * K) + 7 ≤ 5000 * s ^ 5 * K
  nlinarith

theorem program_run_bounded (ctx : Context) (pairs : List PlanPair) (B : ℕ)
    (hc : ctx.Valid) (hv : ∀ pair ∈ pairs, ValidPair ctx pair)
    (hA : 1 ≤ ctx.alphabet.length) (hcur : ctx.current.flatten.length ≤ B)
    (hw : ctx.width.length ≤ B) (hd : ctx.depth.length ≤ B) (hn : pairs.length ≤ B)
    (hp : ∀ pair ∈ pairs, (pairBytes pair).length ≤ B) :
    RunsIn program (5000 * (B + 1) ^ 5 * ctx.alphabet.length ^ ctx.depth.length)
      ((inputState ctx pairs).withPC (some program.entry))
      ((outputState ctx pairs).withPC none) := by
  obtain ⟨n, hn', ht⟩ := program_run ctx pairs hc hv
  exact ⟨n, hn'.trans (sourceBudget_le ctx pairs B hA
    (fun row hrow => (hc.2 row hrow).le) hcur hw hd hn hp), ht⟩

theorem primitive_run_bounded (ctx : Context) (pairs : List PlanPair) (B : ℕ)
    (hc : ctx.Valid) (hv : ∀ pair ∈ pairs, ValidPair ctx pair)
    (hA : 1 ≤ ctx.alphabet.length) (hcur : ctx.current.flatten.length ≤ B)
    (hw : ctx.width.length ≤ B) (hd : ctx.depth.length ≤ B) (hn : pairs.length ≤ B)
    (hp : ∀ pair ∈ pairs, (pairBytes pair).length ≤ B) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (5000 * (B + 1) ^ 5 * ctx.alphabet.length ^ ctx.depth.length))
      (primitiveCfg program ((inputState ctx pairs).withPC (some program.entry)))
      (primitiveCfg program ((outputState ctx pairs).withPC none)) :=
  primitive_execution program (program_run_bounded ctx pairs B hc hv hA hcur hw hd hn hp)

/-- Only physically stored lists occur in this parameter. -/
def physicalSize (ctx : Context) (pairs : List PlanPair) : ℕ :=
  ctx.current.flatten.length + ctx.width.length + ctx.depth.length + (pairRecords pairs).length

theorem sourceBudget_le_physicalSize (ctx : Context) (pairs : List PlanPair)
    (hA : 1 ≤ ctx.alphabet.length)
    (ha : ∀ row ∈ ctx.alphabet, row.length ≤ ctx.width.length) :
    sourceBudget ctx pairs ≤
      5000 * (physicalSize ctx pairs + 1) ^ 5 * ctx.alphabet.length ^ ctx.depth.length := by
  apply sourceBudget_le ctx pairs (physicalSize ctx pairs) hA ha
  · unfold physicalSize; omega
  · unfold physicalSize; omega
  · unfold physicalSize; omega
  · have h := pair_count_le_encoded pairs
    unfold physicalSize; omega
  · intro pair hpair
    have h := pair_length_le_encoded pairs pair hpair
    unfold physicalSize; omega

end SubexponentialSAT.Subexp.PairRuntimeBounds

end OAI.Algorithms
