import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PairPreparationProgram

namespace OAI.Algorithms

/-! Uniform polynomial bounds for the actual once-per-step pair preparation
program. The common parameter bounds physical input lengths and record count. -/

namespace SubexponentialSAT.Subexp.PairPreparationBounds

open BitProgram PairPreparationProgram

private theorem sum_le_length_mul (xs : List ℕ) (B : ℕ) (h : ∀ n ∈ xs, n ≤ B) :
    xs.sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons n ns ih =>
    have hn := h n (by simp)
    have ht := ih (fun m hm => h m (by simp [hm]))
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem member_le_sum {n : ℕ} {xs : List ℕ} (h : n ∈ xs) : n ≤ xs.sum := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := ih h; simp only [List.sum_cons]; omega

theorem planBytes_eq (plan : List ℕ) :
    CollisionStreamProgram.planBytes plan =
      ProgramEncoding.encodeRecords (plan.map SelectionTableProgram.unary) := rfl

theorem planBytes_length (plan : List ℕ) :
    (CollisionStreamProgram.planBytes plan).length = 2 * plan.sum + 2 * plan.length + 1 :=
  GatherProgram.encoded_plan_length plan

theorem plan_sizes_le (plan : List ℕ) :
    plan.sum ≤ (CollisionStreamProgram.planBytes plan).length ∧
      plan.length ≤ (CollisionStreamProgram.planBytes plan).length := by
  rw [planBytes_length]
  omega

theorem pair_plan_lengths (pair : PlanPair) :
    (CollisionStreamProgram.planBytes pair.1).length ≤ (PairScoreProgram.pairBytes pair).length ∧
      (CollisionStreamProgram.planBytes pair.2).length ≤ (PairScoreProgram.pairBytes pair).length := by
  simp only [PairScoreProgram.pairBytes, List.length_append, Encoding.length_frame]
  omega

theorem encoded_pairRecords_le (pairs : List PlanPair) (W : ℕ)
    (h : ∀ pair ∈ pairs, (PairScoreProgram.pairBytes pair).length ≤ W) :
    (PairScoreProgram.pairRecords pairs).length ≤ 1 + (2 * W + 2) * pairs.length := by
  have he := ProgramEncoding.encodeRecords_length_le (pairs.map PairScoreProgram.pairBytes) W (by
    intro bytes hbytes
    obtain ⟨pair, hp, rfl⟩ := List.mem_map.mp hbytes
    exact h pair hp)
  simpa only [PairScoreProgram.pairRecords, List.length_map] using he

theorem planBytes_le (plan : List ℕ) (W : ℕ) (h : ∀ n ∈ plan, n ≤ W) :
    (CollisionStreamProgram.planBytes plan).length ≤ 1 + (2 * W + 2) * plan.length := by
  rw [planBytes_eq]
  have he := ProgramEncoding.encodeRecords_length_le (plan.map SelectionTableProgram.unary) W (by
    intro bytes hbytes
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hbytes
    simpa [SelectionTableProgram.unary] using h n hn)
  simpa only [List.length_map] using he

theorem remaining_length_le (M processed : ℕ) (pair : PlanPair) :
    (remaining M processed pair).length ≤ M := by
  simpa [remaining, ActivePlanProgram.active] using
    List.length_filter_le (fun n => decide (processed + 1 ≤ n ∧ n ∈ pair.1.reverse ++ pair.2))
      (List.range M)

theorem remaining_member_lt (M processed : ℕ) (pair : PlanPair) (n : ℕ)
    (hn : n ∈ remaining M processed pair) : n < M := by
  have h := (ActivePlanProgram.mem_active (List.range M) (pair.1.reverse ++ pair.2)
    (processed + 1) n).mp hn
  exact List.mem_range.mp h.1

theorem remaining_sum_le (M processed : ℕ) (pair : PlanPair) :
    (remaining M processed pair).sum ≤ M * M := by
  exact (sum_le_length_mul _ M (fun n hn =>
    Nat.le_of_lt (remaining_member_lt M processed pair n hn))).trans
      (Nat.mul_le_mul_right M (remaining_length_le M processed pair))

theorem seedBytes_length_le (M : ℕ) : (seedBytes M).length ≤ 3 * (M + 1)^2 := by
  have h := planBytes_le (List.range M) M (fun n hn => Nat.le_of_lt (List.mem_range.mp hn))
  change (seedBytes M).length ≤ _ at h
  simp only [List.length_range] at h
  nlinarith

theorem remainingBytes_length_le (M processed : ℕ) (pair : PlanPair) :
    (CollisionStreamProgram.planBytes (remaining M processed pair)).length ≤ 3 * (M + 1)^2 := by
  have h := planBytes_le (remaining M processed pair) M
    (fun n hn => Nat.le_of_lt (remaining_member_lt M processed pair n hn))
  have hl := remaining_length_le M processed pair
  calc
    _ ≤ 1 + (2 * M + 2) * M := h.trans (by gcongr)
    _ ≤ _ := by nlinarith

theorem tableBytes_length_le (M processed : ℕ) (pair : PlanPair) :
    (SelectionTableProgram.tableBytes M (remaining M processed pair)).length ≤ 2 * (M + 1)^3 := by
  have h := SelectionTableProgram.tableBytes_length_le M (remaining M processed pair)
  have hl := remaining_length_le M processed pair
  have hs := remaining_sum_le M processed pair
  calc
    _ ≤ M * (2 * (M * M) + 2 * (M + M) + 2) := h.trans (by gcongr)
    _ ≤ _ := by ring_nf; omega

theorem tableCost_le (M processed : ℕ) (pair : PlanPair) :
    SelectionTableProgram.traceCost M (remaining M processed pair) ≤ 128 * (M + 1)^4 := by
  have h := SelectionTableProgram.traceCost_quadratic M (remaining M processed pair)
  have hl := remaining_length_le M processed pair
  have hs := remaining_sum_le M processed pair
  calc
    _ ≤ 128 * (M + M * M + M + 1)^2 := h.trans (by gcongr)
    _ = _ := by ring

theorem unionBytes_le (pair : PlanPair) :
    (CollisionStreamProgram.planBytes (pair.1.reverse ++ pair.2)).length ≤
      (CollisionStreamProgram.planBytes pair.1).length +
        (CollisionStreamProgram.planBytes pair.2).length := by
  simp only [planBytes_length, List.sum_append, List.sum_reverse, List.length_append,
    List.length_reverse]
  omega

theorem activeCost_le (ctx : Context) (pair : PlanPair) (B : ℕ)
    (hm : ctx.seedCount ≤ B) (hp : ctx.processedBits.length ≤ B)
    (hb : (PairScoreProgram.pairBytes pair).length ≤ B) :
    ActivePlanProgram.traceBoundThreshold (List.range ctx.seedCount)
      (pair.1.reverse ++ pair.2) (true :: ctx.processedBits) ≤ 4096 * (B + 1)^4 := by
  have hu := unionBytes_le pair
  have hl := (pair_plan_lengths pair).1.trans hb
  have hr := (pair_plan_lengths pair).2.trans hb
  have hseed : (seedBytes ctx.seedCount).length ≤ 3 * (B + 1)^2 :=
    (seedBytes_length_le _).trans (by gcongr)
  have h := ActivePlanProgram.sourceBound_le
    (ActivePlanProgram.indexRecords (pair.1.reverse ++ pair.2))
    (ActivePlanProgram.indexRecords (List.range ctx.seedCount)) (true :: ctx.processedBits)
  change ActivePlanProgram.traceBoundThreshold _ _ _ ≤
    256 * ((CollisionStreamProgram.planBytes (pair.1.reverse ++ pair.2)).length +
      (true :: ctx.processedBits).length + 1) * ((seedBytes ctx.seedCount).length + 1) at h
  have hu' : (CollisionStreamProgram.planBytes (pair.1.reverse ++ pair.2)).length ≤ 2 * B := by omega
  have hp' : (true :: ctx.processedBits).length ≤ B + 1 := by simpa using Nat.add_le_add_right hp 1
  calc
    _ ≤ 256 * (2 * B + (B + 1) + 1) * (3 * (B + 1)^2 + 1) := h.trans (by gcongr)
    _ ≤ _ := by ring_nf; omega

theorem selectorCost_le (ctx : Context) (pair : PlanPair) (B : ℕ)
    (hm : ctx.seedCount ≤ B) (hb : (PairScoreProgram.pairBytes pair).length ≤ B) :
    SelectorPairProgram.cost
      (SelectorProgram.selectionEntries ctx.seedCount (remaining ctx.seedCount ctx.processedBits.length pair))
      (pair.1.map SelectionTableProgram.unary).reverse
      (pair.2.map SelectionTableProgram.unary).reverse ≤ 6600 * (B + 1)^4 := by
  have hl := (pair_plan_lengths pair).1.trans hb
  have hr := (pair_plan_lengths pair).2.trans hb
  have ht : (SelectionTableProgram.tableBytes ctx.seedCount
      (remaining ctx.seedCount ctx.processedBits.length pair)).length ≤ 2 * (B + 1)^3 :=
    (tableBytes_length_le _ _ _).trans (by gcongr)
  have h := SelectorPairProgram.cost_bound
    (SelectorProgram.selectionEntries ctx.seedCount (remaining ctx.seedCount ctx.processedBits.length pair))
    (pair.1.map SelectionTableProgram.unary).reverse
    (pair.2.map SelectionTableProgram.unary).reverse
  rw [← SelectionTableProgram.tableBytes_eq_rawRecords] at h
  simp only [ProgramEncoding.encodeRecords, ActivePlanProgram.encoded_reverse_length] at h
  change _ ≤ 1100 * (_ + 1) * ((CollisionStreamProgram.planBytes pair.1).length +
    (CollisionStreamProgram.planBytes pair.2).length + 1) at h
  calc
    _ ≤ 1100 * (2 * (B + 1)^3 + 1) * (B + B + 1) := h.trans (by gcongr)
    _ ≤ _ := by ring_nf; omega

theorem callbackCost_le (ctx : Context) (pair : PlanPair) (B : ℕ)
    (hm : ctx.seedCount ≤ B) (hp : ctx.processedBits.length ≤ B)
    (hb : (PairScoreProgram.pairBytes pair).length ≤ B) :
    callbackCost ctx pair ≤ 20000 * (B + 1)^4 := by
  have hl := (pair_plan_lengths pair).1.trans hb
  have hr := (pair_plan_lengths pair).2.trans hb
  have hu : (CollisionStreamProgram.planBytes (pair.1.reverse ++ pair.2)).length ≤ 2 * B := by
    have h := unionBytes_le pair; omega
  have hseed : (seedBytes ctx.seedCount).length ≤ 3 * (B + 1)^2 :=
    (seedBytes_length_le _).trans (by gcongr)
  have hrem : (CollisionStreamProgram.planBytes
      (remaining ctx.seedCount ctx.processedBits.length pair)).length ≤ 3 * (B + 1)^2 :=
    (remainingBytes_length_le _ _ _).trans (by gcongr)
  have hremLen := (remaining_length_le ctx.seedCount ctx.processedBits.length pair).trans hm
  have htable : (SelectionTableProgram.tableBytes ctx.seedCount
      (remaining ctx.seedCount ctx.processedBits.length pair)).length ≤ 2 * (B + 1)^3 :=
    (tableBytes_length_le _ _ _).trans (by gcongr)
  have htableCost : SelectionTableProgram.traceCost ctx.seedCount
      (remaining ctx.seedCount ctx.processedBits.length pair) ≤ 128 * (B + 1)^4 :=
    (tableCost_le _ _ _).trans (by gcongr)
  have ha := activeCost_le ctx pair B hm hp hb
  have hs := selectorCost_le ctx pair B hm hb
  have hparse : PairPlanPreparation.parseCost
      (pair.1.map SelectionTableProgram.unary) (pair.2.map SelectionTableProgram.unary) ≤
      21 * B + 17 := by
    change 3 * (PairScoreProgram.pairBytes pair).length + 9 *
      ((CollisionStreamProgram.planBytes pair.1).length +
        (CollisionStreamProgram.planBytes pair.2).length) + 17 ≤ _
    omega
  have hcoarse : callbackCost ctx pair ≤
      (21 * B + 17) + (24 * B + 10) + (21 * (B + 1)^2 + 5) + 4096 * (B + 1)^4 +
      (4 * B + 3) + (27 * (B + 1)^2 + 8) + (7 * B + 5) + 3 + 128 * (B + 1)^4 +
      (4 * B + 3) + (20 * B + 9) + 6600 * (B + 1)^4 + (4 * (B + 1)^3 + 3) + 13 := by
    unfold callbackCost
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero]
    have hmap : (pair.1.map SelectionTableProgram.unary).reverse ++
        pair.2.map SelectionTableProgram.unary =
        (pair.1.reverse ++ pair.2).map SelectionTableProgram.unary := by simp
    rw [hmap]
    change _ ≤ _ at hrem
    change (ProgramEncoding.encodeRecords
      ((pair.1.reverse ++ pair.2).map SelectionTableProgram.unary)).length ≤ _ at hu
    change (ProgramEncoding.encodeRecords (pair.1.map SelectionTableProgram.unary)).length ≤ _ at hl
    change (ProgramEncoding.encodeRecords (pair.2.map SelectionTableProgram.unary)).length ≤ _ at hr
    change (ProgramEncoding.encodeRecords
      ((remaining ctx.seedCount ctx.processedBits.length pair).map SelectionTableProgram.unary)).length ≤ _ at hrem
    omega
  exact hcoarse.trans (by ring_nf; omega)

theorem loopCost_le (ctx : Context) (pairs : List PlanPair) (B : ℕ)
    (hm : ctx.seedCount ≤ B) (hp : ctx.processedBits.length ≤ B)
    (hb : ∀ pair ∈ pairs, (PairScoreProgram.pairBytes pair).length ≤ B) :
    loopCost ctx pairs ≤ 1 + pairs.length * (20000 * (B + 1)^4 + 6 * B + 7) := by
  induction pairs with
  | nil => simp [loopCost]
  | cons pair pairs ih =>
    have hpair := hb pair (by simp)
    have hc := callbackCost_le ctx pair B hm hp hpair
    have ht := ih (fun q hq => hb q (by simp [hq]))
    simp only [loopCost, List.length_cons]
    nlinarith

theorem selectedPair_length_le (ctx : Context) (pair : PlanPair) (B : ℕ)
    (hm : ctx.seedCount ≤ B) (hb : (PairScoreProgram.pairBytes pair).length ≤ B) :
    (PairScoreProgram.pairBytes (selectedPair ctx.seedCount ctx.processedBits.length pair)).length ≤
      30 * (B + 1)^2 := by
  have hl := (pair_plan_lengths pair).1.trans hb
  have hr := (pair_plan_lengths pair).2.trans hb
  have hleft := plan_sizes_le pair.1
  have hright := plan_sizes_le pair.2
  have hrem := (remaining_length_le ctx.seedCount ctx.processedBits.length pair).trans hm
  have hselect : ∀ n, n ≤ B → ReadPlan.selectPosition ctx.seedCount
      (remaining ctx.seedCount ctx.processedBits.length pair) n ≤ 2 * B := by
    intro n hn
    unfold ReadPlan.selectPosition
    split
    · have hi : (remaining ctx.seedCount ctx.processedBits.length pair).idxOf n ≤
          (remaining ctx.seedCount ctx.processedBits.length pair).length := List.idxOf_le_length
      omega
    · omega
  have hplan : ∀ plan : List ℕ, plan.sum ≤ B → plan.length ≤ B →
      (CollisionStreamProgram.planBytes (plan.map (ReadPlan.selectPosition ctx.seedCount
        (remaining ctx.seedCount ctx.processedBits.length pair)))).length ≤ 7 * (B + 1)^2 := by
    intro plan hsum hlen
    have h := planBytes_le (plan.map (ReadPlan.selectPosition ctx.seedCount
      (remaining ctx.seedCount ctx.processedBits.length pair))) (2 * B) (by
        intro n hn
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hn
        exact hselect k ((member_le_sum hk).trans hsum))
    simp only [List.length_map] at h
    calc
      _ ≤ 1 + (2 * (2 * B) + 2) * B := h.trans (by gcongr)
      _ ≤ _ := by nlinarith
  have hsleft := hplan pair.1 (hleft.1.trans hl) (hleft.2.trans hl)
  have hsright := hplan pair.2 (hright.1.trans hr) (hright.2.trans hr)
  simp only [PairScoreProgram.pairBytes, selectedPair, List.length_append, Encoding.length_frame]
  nlinarith

theorem selectedPairs_bytes_length_le (ctx : Context) (B : ℕ)
    (hm : ctx.seedCount ≤ B) (hn : ctx.pairs.length ≤ B)
    (hb : ∀ pair ∈ ctx.pairs, (PairScoreProgram.pairBytes pair).length ≤ B) :
    (PairScoreProgram.pairRecords
      (selectedPairs ctx.seedCount ctx.processedBits.length ctx.pairs)).length ≤ 63 * (B + 1)^3 := by
  have h := encoded_pairRecords_le (selectedPairs ctx.seedCount ctx.processedBits.length ctx.pairs)
    (30 * (B + 1)^2) (by
      intro pair hpair
      obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hpair
      exact selectedPair_length_le ctx p B hm (hb p hp'))
  simp only [selectedPairs, List.length_map] at h
  calc
    _ ≤ 1 + (2 * (30 * (B + 1)^2) + 2) * B := h.trans (by gcongr)
    _ ≤ _ := by ring_nf; omega

theorem traceBound_le (ctx : Context) (B : ℕ)
    (hm : ctx.seedCount ≤ B) (hp : ctx.processedBits.length ≤ B)
    (hn : ctx.pairs.length ≤ B)
    (hb : ∀ pair ∈ ctx.pairs, (PairScoreProgram.pairBytes pair).length ≤ B) :
    traceBound ctx ≤ 30000 * (B + 1)^5 := by
  have hraw : (PairScoreProgram.pairRecords ctx.pairs).length ≤ 3 * (B + 1)^2 := by
    have h := encoded_pairRecords_le ctx.pairs B hb
    calc
      _ ≤ 1 + (2 * B + 2) * B := h.trans (by gcongr)
      _ ≤ _ := by nlinarith
  have hsel := selectedPairs_bytes_length_le ctx B hm hn hb
  have hrev : (PairScoreProgram.pairRecords
      (selectedPairs ctx.seedCount ctx.processedBits.length ctx.pairs).reverse).length =
      (PairScoreProgram.pairRecords
        (selectedPairs ctx.seedCount ctx.processedBits.length ctx.pairs)).length := by
    simp only [PairScoreProgram.pairRecords, List.map_reverse, ProgramEncoding.encodeRecords,
      ActivePlanProgram.encoded_reverse_length]
  have hloop : loopCost ctx ctx.pairs ≤ 21000 * (B + 1)^5 := by
    have h := loopCost_le ctx ctx.pairs B hm hp hb
    calc
      _ ≤ 1 + B * (20000 * (B + 1)^4 + 6 * B + 7) := h.trans (by gcongr)
      _ ≤ _ := by ring_nf; omega
  dsimp only [traceBound]
  rw [hrev]
  calc
    _ ≤ 7 * (3 * (B + 1)^2) + 5 + (7 * B + 5) + 2 + 2 + 16 +
        (2 + 21000 * (B + 1)^5) + (2 * (B + 1) + 3) + 2 +
        10 * (63 * (B + 1)^3) + (9 * (63 * (B + 1)^3) + 8) + 16 + 1 := by omega
    _ ≤ _ := by ring_nf; omega

theorem program_runsIn (ctx : Context) (B : ℕ) (regs : Fin 16 → Bool)
    (hm : ctx.seedCount ≤ B) (hp : ctx.processedBits.length ≤ B)
    (hn : ctx.pairs.length ≤ B)
    (hb : ∀ pair ∈ ctx.pairs, (PairScoreProgram.pairBytes pair).length ≤ B) :
    RunsIn PairPreparationProgram.program (30000 * (B + 1)^5)
      ((inputState ctx regs).withPC (some PairPreparationProgram.program.entry))
      ((outputState ctx).withPC none) := by
  obtain ⟨n, hn', ht⟩ := PairPreparationProgram.program_runsIn ctx regs
  exact ⟨n, hn'.trans (traceBound_le ctx B hm hp hn hb), ht⟩

theorem primitive_runsIn (ctx : Context) (B : ℕ) (regs : Fin 16 → Bool)
    (hm : ctx.seedCount ≤ B) (hp : ctx.processedBits.length ≤ B)
    (hn : ctx.pairs.length ≤ B)
    (hb : ∀ pair ∈ ctx.pairs, (PairScoreProgram.pairBytes pair).length ≤ B) :
    Computation.RunsIn (primitive PairPreparationProgram.program).step
      (primitiveOverhead PairPreparationProgram.program * (30000 * (B + 1)^5))
      (primitiveCfg PairPreparationProgram.program
        ((inputState ctx regs).withPC (some PairPreparationProgram.program.entry)))
      (primitiveCfg PairPreparationProgram.program ((outputState ctx).withPC none)) :=
  primitive_execution PairPreparationProgram.program (program_runsIn ctx B regs hm hp hn hb)

end SubexponentialSAT.Subexp.PairPreparationBounds

end OAI.Algorithms
