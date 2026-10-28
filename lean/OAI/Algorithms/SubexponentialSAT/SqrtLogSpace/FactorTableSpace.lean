import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
import Mathlib.Tactic.GCongr

/-! Space for one actual ambient-coordinate table construction. Its unary
traversal has only n iterations, so its polynomial local time bounds every
source prefix. No outer signature or finite-difference iteration count occurs
in this estimate. The concrete literal and staging traces are instantiated by
the factor-table producer, rather than supplied to a final counting endpoint. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace

open SqrtLog

open BitProgram StructuredCalls FactorTableProgram

/-- Includes the master's copy, all literal visits, output move and final halt. -/
def tableBudget (n K L : ℕ) : ℕ :=
  7 * n + n * (K + 2) + 6 * (n * (2 * n + 2 * L + 4)) + 16

/-- The entire native table construction costs a fixed quadratic polynomial
in the per-literal budget, ambient dimension and specialized payload width. -/
theorem tableBudget_le (n K L : ℕ) :
    tableBudget n K L ≤ 64 * (n + K + L + 1) ^ 2 := by
  let T := n + K + L + 1
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hn : n ≤ T := by dsimp [T]; omega
  have hK : K ≤ T := by dsimp [T]; omega
  have hrow : 2 * n + 2 * L + 4 ≤ 4 * T := by dsimp [T]; omega
  have htable : n * (2 * n + 2 * L + 4) ≤ T * (4 * T) :=
    Nat.mul_le_mul hn hrow
  have hbody : n * (K + 2) ≤ T * (T + 2) :=
    Nat.mul_le_mul hn (Nat.add_le_add_right hK 2)
  have hsquare : T ≤ T ^ 2 := by nlinarith
  change 7 * n + n * (K + 2) + 6 * (n * (2 * n + 2 * L + 4)) + 16 ≤ 64 * T ^ 2
  nlinarith

/-- The unary ambient loop itself has one actual existential payload family
and an all-prefix bound linear in its paid number of native body calls. -/
theorem literalLoop_resources (s : OuterStore) (body : OuterCode)
    (P : ℕ → List Bool → Prop) (K n L B : ℕ)
    (hbody : RelLiteralBody s body P K n L)
    (hinitial : ∀ i, ((literalReady s (List.replicate n true) []) i).length ≤ B)
    (regs : Fin 16 → Bool) :
    let p := compiled (UnaryForPrograms.forCmd literalPorts body) 573 569
    ∃ payload steps rf, (∀ j, j < n → (payload j).length ≤ L ∧ P j (payload j)) ∧
      steps ≤ n * (K + 2) + 3 ∧
      Trace p steps
        ((⟨regs, literalReady s (List.replicate n true) []⟩ : OuterData).withPC
          (some p.entry))
        ((⟨rf, literalReady s [] (tableResult payload n [])⟩ : OuterData).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace p prefixSteps
          ((⟨regs, literalReady s (List.replicate n true) []⟩ : OuterData).withPC
            (some p.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896 * B + (n * (K + 2) + 3) := by
  dsimp only
  obtain ⟨payload, steps, rf, hpayload, hsteps, heval⟩ :=
    literalLoop_rel_run s body P K n L hbody n le_rfl [] (by simp) regs
  have htime : steps + 1 ≤ n * (K + 2) + 3 := by omega
  refine ⟨payload, steps + 1, rf, hpayload, htime, compiled_halt_trace heval 573 569, ?_⟩
  intro prefixSteps intermediate hp ht i
  exact StructuredSpace.local_stack_bound
    (compiled (UnaryForPrograms.forCmd literalPorts body) 573 569)
    (StreamResources.dataBits_le_mul _ hinitial) prefixSteps intermediate
    (hp.trans htime) ht i

/-- The actual run chooses each specialized payload after receiving its
register state. The same witness supplies exact table output, time and every
source-prefix bound; no register-uniform byte family is assumed. -/
theorem prepareFactor_resources (s : OuterStore) (P : ℕ → List Bool → Prop)
    (K n L B : ℕ) (hn : s 552 = List.replicate n true)
    (h460 : s 460 = []) (h573 : s 573 = []) (h569 : s 569 = [])
    (h561 : s 561 = []) (h585 : s 585 = [])
    (hbody : RelLiteralBody s literalIteration P K n L)
    (hinitial : ∀ i, (s i).length ≤ B) (regs : Fin 16 → Bool) :
    let p := compiled prepareFactor 552 561
    ∃ payload steps rf, (∀ j, j < n → (payload j).length ≤ L ∧ P j (payload j)) ∧
      steps ≤ tableBudget n K L ∧
      Trace p steps ((⟨regs, s⟩ : OuterData).withPC (some p.entry))
        ((⟨rf, Function.update s 561 (tableResult payload n [])⟩ : OuterData).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace p prefixSteps ((⟨regs, s⟩ : OuterData).withPC (some p.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896 * B + tableBudget n K L := by
  dsimp only
  obtain ⟨payload, steps, rf, hpayload, hsteps, heval⟩ :=
    prepareFactor_rel_run s P K n L hn h460 h573 h569 h561 h585 hbody regs
  have htime : steps + 1 ≤ tableBudget n K L := by
    dsimp only [tableBudget, literalRecordBound] at *
    nlinarith
  refine ⟨payload, steps + 1, rf, hpayload, htime, compiled_halt_trace heval 552 561, ?_⟩
  intro prefixSteps intermediate hp ht i
  exact StructuredSpace.local_stack_bound (compiled prepareFactor 552 561)
    (StreamResources.dataBits_le_mul _ hinitial) prefixSteps intermediate
    (hp.trans htime) ht i

/-- Entry clearing is paid using the incoming word lengths, including garbage
in private scratch. Its bound includes the compiled return/halt instruction. -/
theorem initialize_resources (a : OuterData) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    let p := compiled initializeWorker 556 62
    ∃ steps, steps ≤ entryPorts.length * (2 * B + 3) + 1 ∧
      Trace p steps (a.withPC (some p.entry)) ((initialized a).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace p prefixSteps (a.withPC (some p.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          896 * B + (entryPorts.length * (2 * B + 3) + 1) := by
  dsimp only
  have hcost := SubexpSetupStorage.clearManyCost_le entryPorts a B hb
  refine ⟨SubexpSetupStorage.clearManyCost entryPorts a + 1,
    Nat.add_le_add_right hcost 1, compiled_halt_trace (initialize_eval a) 556 62, ?_⟩
  intro prefixSteps intermediate hp ht i
  exact StructuredSpace.local_stack_bound (compiled initializeWorker 556 62)
    (StreamResources.dataBits_le_mul _ hb) prefixSteps intermediate
    (hp.trans (Nat.add_le_add_right hcost 1)) ht i

/-- The eighteen physical copies have sources disjoint from every destination. -/
theorem original_stageCost_le (a : LeafProgram.Incidence.Data) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    LeafProgram.Incidence.stageCost a ≤ 133 * B + 97 := by
  have hc := SubexpSetupStorage.copyManyCost_le LeafProgram.Incidence.pairs a B
    (ha := fun p _ => hb p.1) (by
      intro p hp q hq
      have hsource : p.1.val < 340 ∨ 700 ≤ p.1.val := by
        simp only [LeafProgram.Incidence.pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide
      have hdest : 340 ≤ q.2.val ∧ q.2.val < 700 := by
        simp only [LeafProgram.Incidence.pairs, List.mem_cons, List.mem_nil_iff, or_false] at hq
        rcases hq with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst q <;> decide
      intro he
      have hv := congrArg Fin.val he
      omega)
  have hr := hb 138
  change SubexpSetupStorage.copyManyCost LeafProgram.Incidence.pairs a ≤ 18 * (7 * B + 5) at hc
  dsimp only [LeafProgram.Incidence.stageCost]
  omega

/-- Clearing private scratch cannot increase any incoming stack. -/
theorem initialized_stack_bound (a : OuterData) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((initialized a).stacks i).length ≤ B := by
  intro i
  rw [initialized, SubexpSetupStorage.clearMany_stacks]
  split
  · simp
  · exact hb i

/-- Every actual external source master survives entry clearing, including
masters702/703 and710..728; no initial scratch-blank premise is used. -/
theorem initialized_base_external (a : OuterData) (i : Fin 768)
    (hi : (i.val < 340 ∧ i ≠ 62) ∨ 684 < i.val) :
    (initialized a).stacks (basePort i) = a.stacks (basePort i) := by
  have hn (j : Fin 768) (hj : 340 ≤ j.val ∧ j.val ≤ 684) : i ≠ j := by
    intro hij
    subst j
    rcases hi with hi | hi <;> omega
  have hbase : basePort i = i.castAdd 128 := by
    simp only [basePort, ite_eq_right (hn 640 (by decide)), ite_eq_right (hn 641 (by decide)),
      ite_eq_right (hn 642 (by decide)), ite_eq_right (hn 647 (by decide)),
      ite_eq_right (hn 650 (by decide)), ite_eq_right (hn 651 (by decide)),
      ite_eq_right (hn 670 (by decide)), ite_eq_right (hn 671 (by decide))]
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_right]
  simp only [entryPorts, List.mem_append]
  rintro (h | h)
  · obtain ⟨j, hj, he⟩ := List.mem_map.mp h
    have hji : j = i := basePort_injective he
    subst j
    have hw := (LeafProgram.Incidence.mem_workerPorts i).mp (List.mem_filter.mp hj).1
    rcases hi with hi | hi <;> omega
  · rw [hbase] at h
    have hnum : (i.val < 340 ∧ i.val ≠ 62) ∨ 684 < i.val := by
      rcases hi with ⟨hlt, hne⟩ | hgt
      · exact Or.inl ⟨hlt, fun hv => hne (Fin.ext hv)⟩
      · exact Or.inr hgt
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Fin.ext_iff,
      Fin.val_castAdd, Fin.coe_ofNat_eq_mod] at h
    norm_num at h
    omega

/-- The relocated stage includes its compiled call instruction. -/
theorem stageCost_le (a : OuterData) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) : stageCost a ≤ 133 * B + 98 := by
  have h := original_stageCost_le (projectState id basePort (initialized a)) B
    (fun i => initialized_stack_bound a B hb (basePort i))
  dsimp only [stageCost]
  omega

/-- All staging copies, the cutoff copy and both call and halt instructions
are counted on the same source run. -/
theorem stage_resources (a : OuterData) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    let p := compiled (liftBase LeafProgram.Incidence.stage) 556 62
    ∃ steps, steps ≤ 133 * B + 99 ∧
      Trace p steps ((initialized a).withPC (some p.entry)) ((staged a).withPC none) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace p prefixSteps ((initialized a).withPC (some p.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896 * B + (133 * B + 99) := by
  dsimp only
  have hc : stageCost a + 1 ≤ 133 * B + 99 := by have := stageCost_le a B hb; omega
  refine ⟨stageCost a + 1, hc, compiled_halt_trace (stage_eval a) 556 62, ?_⟩
  intro prefixSteps intermediate hp ht i
  exact StructuredSpace.local_stack_bound (compiled (liftBase LeafProgram.Incidence.stage) 556 62)
    (StreamResources.dataBits_le_mul _ (initialized_stack_bound a B hb))
    prefixSteps intermediate (hp.trans hc) ht i

/-- The output is copied into its freshly cleared destination before all340
private source stacks are reclaimed. -/
theorem original_exportCost_le (a : LeafProgram.Incidence.Data) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) (h62 : a.stacks 62 = []) :
    LeafProgram.Incidence.exportCost a ≤ 687 * B + 1025 := by
  have hcopy : ∀ i, ((SubexpSetupStorage.copyState 561 62 a).stacks i).length ≤ B := by
    intro i
    by_cases hi : i = 62
    · subst i
      simpa [SubexpSetupStorage.copyState_stack, h62] using hb 561
    · simpa [SubexpSetupStorage.copyState_stack, hi] using hb i
  have hc := SubexpSetupStorage.clearManyCost_le LeafProgram.Incidence.workerPorts
    (SubexpSetupStorage.copyState 561 62 a) B hcopy
  have hlen : LeafProgram.Incidence.workerPorts.length = 340 := by
    simp only [LeafProgram.Incidence.workerPorts, List.length_map, List.length_finRange]
  rw [hlen] at hc
  have hr := hb 561
  dsimp only [LeafProgram.Incidence.exportCost]
  omega

/-- One additional instruction invokes the relocated exporter. -/
theorem exportCost_le (a : OuterData) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) (h62 : a.stacks 62 = []) :
    exportCost a ≤ 687 * B + 1026 := by
  have h := original_exportCost_le (projectState id basePort a) B
    (fun i => hb (basePort i)) h62
  dsimp only [exportCost]
  omega

/-- The exact exported table word and every caller stack share one trace. -/
theorem export_resources (a : OuterData) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) (h62 : a.stacks 62 = [])
    (htmp : a.stacks 684 = []) :
    let p := compiled (liftBase LeafProgram.Incidence.exportResult) 556 62
    ∃ steps, steps ≤ 687 * B + 1027 ∧
      Trace p steps (a.withPC (some p.entry)) ((exported a).withPC none) ∧
      (exported a).stacks 62 = a.stacks 561 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace p prefixSteps (a.withPC (some p.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896 * B + (687 * B + 1027) := by
  dsimp only
  have hc : exportCost a + 1 ≤ 687 * B + 1027 := by have := exportCost_le a B hb h62; omega
  refine ⟨exportCost a + 1, hc, compiled_halt_trace (export_eval a htmp) 556 62,
    exported_output a h62, ?_⟩
  intro prefixSteps intermediate hp ht i
  exact StructuredSpace.local_stack_bound (compiled (liftBase LeafProgram.Incidence.exportResult) 556 62)
    (StreamResources.dataBits_le_mul _ hb) prefixSteps intermediate (hp.trans hc) ht i

private theorem original_staged_frame (a : LeafProgram.Incidence.Data) (i : Fin 768)
    (hi : i = 62 ∨ i = 684) : (LeafProgram.Incidence.staged a).stacks i = a.stacks i := by
  have h550 : i ≠ 550 := by rcases hi with rfl | rfl <;> decide
  change Function.update (SubexpSetupStorage.copyManyState LeafProgram.Incidence.pairs a).stacks
    550 _ i = a.stacks i
  rw [Function.update_of_ne h550]
  apply SubexpSetupStorage.copyMany_frame
  intro p hp
  simp only [LeafProgram.Incidence.pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;>
    rcases hi with rfl | rfl <;> decide

/-- Entry clearing and the paid staging leave the export destination empty. -/
theorem staged_output (a : OuterData) : (staged a).stacks 62 = [] := by
  change (staged a).stacks (basePort 62) = []
  rw [staged, embedState_stack _ _ _ _ basePort_injective,
    original_staged_frame _ 62 (Or.inl rfl)]
  simpa only [projectState, Function.comp_apply,
    show basePort 62 = (62 : Fin 896) from rfl] using initialized_output a

/-- The stage also returns the physical copy temporary empty. -/
theorem staged_temporary (a : OuterData) : (staged a).stacks 684 = [] := by
  change (staged a).stacks (basePort 684) = []
  rw [staged, embedState_stack _ _ _ _ basePort_injective,
    original_staged_frame _ 684 (Or.inr rfl)]
  simpa only [projectState, Function.comp_apply,
    show basePort 684 = (684 : Fin 896) from rfl] using initialized_temporary a

/-- Exactly the ports that may be changed by the table command: relocated
private worker, exported table, and physical copy temporaries. -/
def writtenPorts : List (Fin 896) :=
  LeafProgram.Incidence.workerPorts.map basePort ++ [62,680,681,682,683,684,881,882]

theorem initialized_frame (a : OuterData) (i : Fin 896) (hi : i ∉ writtenPorts) :
    (initialized a).stacks i = a.stacks i := by
  rw [initialized, SubexpSetupStorage.clearMany_stacks, ite_eq_right]
  intro he
  apply hi
  rcases List.mem_append.mp he with he | he
  · obtain ⟨j, hj, hji⟩ := List.mem_map.mp he
    exact List.mem_append_left _ (List.mem_map.mpr ⟨j, (List.mem_filter.mp hj).1, hji⟩)
  · exact List.mem_append_right _ he

private theorem original_staged_worker_frame (a : LeafProgram.Incidence.Data) (i : Fin 768)
    (hi : i ∉ LeafProgram.Incidence.workerPorts) :
    (LeafProgram.Incidence.staged a).stacks i = a.stacks i := by
  have h550 : i ≠ 550 := by
    intro he
    subst i
    exact hi ((LeafProgram.Incidence.mem_workerPorts 550).mpr (by decide))
  change Function.update (SubexpSetupStorage.copyManyState LeafProgram.Incidence.pairs a).stacks
    550 _ i = a.stacks i
  rw [Function.update_of_ne h550]
  apply SubexpSetupStorage.copyMany_frame
  intro p hp he
  apply hi
  rw [he]
  apply (LeafProgram.Incidence.mem_workerPorts p.2).mpr
  simp only [LeafProgram.Incidence.pairs, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst p <;> decide

/-- All caller masters outside the finite write set survive actual staging. -/
theorem staged_frame (a : OuterData) (i : Fin 896) (hi : i ∉ writtenPorts) :
    (staged a).stacks i = a.stacks i := by
  by_cases himage : ∃ j, basePort j = i
  · obtain ⟨j, rfl⟩ := himage
    have hj : j ∉ LeafProgram.Incidence.workerPorts := by
      intro hj
      exact hi (List.mem_append_left _ (List.mem_map.mpr ⟨j, hj, rfl⟩))
    rw [staged, embedState_stack _ _ _ _ basePort_injective,
      original_staged_worker_frame _ j hj]
    simpa only [projectState, Function.comp_apply] using initialized_frame a (basePort j) hi
  · change (embedState id basePort (initialized a) _).stacks i = a.stacks i
    rw [embedState_stack_frame _ _ _ _ i himage]
    exact initialized_frame a i hi

/-- Export and cleanup preserve every caller port outside the write set. -/
theorem exported_frame (a : OuterData) (i : Fin 896) (hi : i ∉ writtenPorts) :
    (exported a).stacks i = a.stacks i := by
  by_cases himage : ∃ j, basePort j = i
  · obtain ⟨j, rfl⟩ := himage
    have hj : j ∉ LeafProgram.Incidence.workerPorts := by
      intro hj
      exact hi (List.mem_append_left _ (List.mem_map.mpr ⟨j, hj, rfl⟩))
    have hj62 : j ≠ 62 := by
      intro he
      subst j
      apply hi
      exact List.mem_append_right _ (by simp [basePort])
    rw [exported, embedState_stack _ _ _ _ basePort_injective,
      LeafProgram.Incidence.exported, SubexpSetupStorage.clearMany_stacks, ite_eq_right hj,
      SubexpSetupStorage.copyState_frame _ _ _ _ hj62]
    rfl
  · exact embedState_stack_frame _ _ _ _ i himage

/-- The exact output state used by the whole command preserves the node
ports, source masters and all other caller words outside its private writes. -/
theorem command_output_frame (a : OuterData) (rf : Fin 16 → Bool) (bytes : List Bool)
    (i : Fin 896) (hi : i ∉ writtenPorts) :
    (exported (⟨rf, Function.update (staged a).stacks 561 bytes⟩ : OuterData)).stacks i =
      a.stacks i := by
  have hi561 : i ≠ 561 := by
    intro he
    subst i
    apply hi
    exact List.mem_append_left _ (List.mem_map.mpr ⟨561,
      (LeafProgram.Incidence.mem_workerPorts 561).mpr (by decide), rfl⟩)
  rw [exported_frame _ i hi]
  change Function.update (staged a).stacks 561 bytes i = a.stacks i
  rw [Function.update_of_ne hi561]
  exact staged_frame a i hi

/-- Actual export clears the complete private worker and every initialized
backup, leaving only the full table on output62. -/
theorem command_output_clean (a : OuterData) (rf : Fin 16 → Bool) (bytes : List Bool)
    (i : Fin 896) (hi : i ∈ writtenPorts) (hne : i ≠ 62) :
    (exported (⟨rf, Function.update (staged a).stacks 561 bytes⟩ : OuterData)).stacks i = [] := by
  have hbase (j : Fin 768) (hj : j ∉ LeafProgram.Incidence.workerPorts)
      (hj62 : j≠62) (hj561 : basePort j≠561) (hentry : basePort j ∈ entryPorts) :
      (exported (⟨rf, Function.update (staged a).stacks 561 bytes⟩ : OuterData)).stacks
        (basePort j) = [] := by
    rw [exported,embedState_stack _ _ _ _ basePort_injective,
      LeafProgram.Incidence.exported,SubexpSetupStorage.clearMany_stacks,ite_eq_right hj,
      SubexpSetupStorage.copyState_frame _ _ _ _ hj62]
    change Function.update (staged a).stacks 561 bytes (basePort j) = []
    rw [Function.update_of_ne hj561,staged,embedState_stack _ _ _ _ basePort_injective,
      original_staged_worker_frame _ j hj]
    change (initialized a).stacks (basePort j) = []
    rw [initialized,SubexpSetupStorage.clearMany_stacks,ite_eq_left hentry]
  have hhigh (j : Fin 896) (hj : j=881 ∨ j=882) :
      (exported (⟨rf, Function.update (staged a).stacks 561 bytes⟩ : OuterData)).stacks j = [] := by
    have hout : ¬∃ v, basePort v=j := by
      apply basePort_outside j
      rcases hj with rfl|rfl <;> exact Or.inr ⟨by decide,Or.inl (by decide)⟩
    have h561 : j≠561 := by rcases hj with rfl|rfl <;> decide
    have hentry : j ∈ entryPorts := by
      apply List.mem_append_right
      rcases hj with rfl|rfl <;> simp
    rw [exported,embedState_stack_frame _ _ _ _ j hout]
    change Function.update (staged a).stacks 561 bytes j = []
    rw [Function.update_of_ne h561,staged,embedState_stack_frame _ _ _ _ j hout,
      initialized,SubexpSetupStorage.clearMany_stacks,ite_eq_left hentry]
  rcases List.mem_append.mp hi with hi|hi
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    rw [exported,embedState_stack _ _ _ _ basePort_injective,
      LeafProgram.Incidence.exported,SubexpSetupStorage.clearMany_stacks,ite_eq_left hj]
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact (hne rfl).elim
    · exact hbase 680 (by rw [LeafProgram.Incidence.mem_workerPorts]; decide)
        (by decide) (by decide) (List.mem_append_right _ (by simp [basePort]))
    · exact hbase 681 (by rw [LeafProgram.Incidence.mem_workerPorts]; decide)
        (by decide) (by decide) (List.mem_append_right _ (by simp [basePort]))
    · exact hbase 682 (by rw [LeafProgram.Incidence.mem_workerPorts]; decide)
        (by decide) (by decide) (List.mem_append_right _ (by simp [basePort]))
    · exact hbase 683 (by rw [LeafProgram.Incidence.mem_workerPorts]; decide)
        (by decide) (by decide) (List.mem_append_right _ (by simp [basePort]))
    · exact hbase 684 (by rw [LeafProgram.Incidence.mem_workerPorts]; decide)
        (by decide) (by decide) (List.mem_append_right _ (by simp [basePort]))
    · exact hhigh 881 (Or.inl rfl)
    · exact hhigh 882 (Or.inr rfl)

/-- Returning a table does not enlarge unrelated caller words. The final
bound is the maximum of the old boundary and the actual exported table word. -/
theorem command_output_stack_bound (a : OuterData) (rf : Fin 16 → Bool)
    (bytes : List Bool) (B : ℕ) (hb : ∀ i, (a.stacks i).length ≤ B) (i : Fin 896) :
    ((exported (⟨rf, Function.update (staged a).stacks 561 bytes⟩ : OuterData)).stacks i).length ≤
      max B bytes.length := by
  by_cases hi : i=62
  · subst i
    have h62 : (⟨rf, Function.update (staged a).stacks 561 bytes⟩ : OuterData).stacks 62=[] := by
      simpa using staged_output a
    rw [exported_output _ h62]
    change bytes.length ≤ max B bytes.length
    exact le_max_right _ _
  · by_cases hw : i∈writtenPorts
    · rw [command_output_clean a rf bytes i hw hi]
      exact Nat.zero_le _
    · rw [command_output_frame a rf bytes i hw]
      exact (hb i).trans (le_max_left _ _)

/-- The protected caller regions include every low node port except the
export62, all eight layout masters, and high ports outside the private bank. -/
theorem caller_port_not_written (i : Fin 896)
    (hi : (i.val < 340 ∧ i ≠ 62) ∨ i ∈ protectedPorts ∨
      (768 ≤ i.val ∧ i ≠ 881 ∧ i ≠ 882 ∧ (i.val < 885 ∨ 892 < i.val))) :
    i ∉ writtenPorts := by
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨j, hj, hji⟩ := List.mem_map.mp hm
    rcases hi with hi | hi | hi
    · have hw := (LeafProgram.Incidence.mem_workerPorts j).mp hj
      have hb : 340 ≤ (basePort j).val := by
        simp only [basePort]
        split_ifs <;> simp_all only [Fin.coe_ofNat_eq_mod, Fin.val_castAdd] <;> omega
      have hv := congrArg Fin.val hji
      omega
    · exact basePort_outside i (Or.inl hi) ⟨j, hji⟩
    · exact basePort_outside i (Or.inr ⟨hi.1, hi.2.2.2⟩) ⟨j, hji⟩
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num [protectedPorts, Fin.ext_iff, Fin.coe_ofNat_eq_mod] at hi

/-- Staging ends within its paid local source-prefix bound. -/
theorem staged_stack_bound (a : OuterData) (B : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((staged a).stacks i).length ≤ 1029 * B + 99 := by
  obtain ⟨steps, _, ht, hprefix⟩ := stage_resources a B hb
  intro i
  have hi := hprefix steps ((staged a).withPC none) le_rfl ht i
  change ((staged a).stacks i).length ≤ 896 * B + (133 * B + 99) at hi
  omega

/-- The middle store retains the old caller data and one polynomial table. -/
def middleBound (B n L : ℕ) : ℕ :=
  1029 * B + 99 + n * literalRecordBound n L

/-- The fixed command pays entry clearing, relocated staging, its ambient
unary table loop, relocated export and final halt. -/
def commandBudget (B n K L : ℕ) : ℕ :=
  entryPorts.length * (2 * B + 3) + (133 * B + 98) + tableBudget n K L +
    (687 * middleBound B n L + 1026) + 1

theorem entryPorts_length_le : entryPorts.length ≤ 348 := by
  have hfilter := List.length_filter_le (fun i : Fin 768 => i ≠ 556)
    LeafProgram.Incidence.workerPorts
  have hworker : LeafProgram.Incidence.workerPorts.length = 340 := by
    simp only [LeafProgram.Incidence.workerPorts, List.length_map, List.length_finRange]
  rw [hworker] at hfilter
  simpa only [entryPorts, List.length_append, List.length_map,
    List.length_cons, List.length_nil] using Nat.add_le_add_right hfilter 8

/-- All pre/postprocessing and the actual table loop fit a fixed quadratic
polynomial; the degree is independent of the input and every traversal count. -/
theorem commandBudget_le (B n K L : ℕ) :
    commandBudget B n K L ≤ 1000000 * (B + n + K + L + 1) ^ 2 := by
  let T := B + n + K + L + 1
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hB : B ≤ T := by dsimp [T]; omega
  have hn : n ≤ T := by dsimp [T]; omega
  have hsq : T ≤ T ^ 2 := by nlinarith
  have hrow : literalRecordBound n L ≤ 4 * T := by
    dsimp [literalRecordBound, T]
    omega
  have htable : n * literalRecordBound n L ≤ 4 * T ^ 2 := by
    have h := Nat.mul_le_mul hn hrow
    nlinarith
  have hmid : middleBound B n L ≤ 1132 * T ^ 2 := by
    dsimp only [middleBound]
    nlinarith
  have hlocal : tableBudget n K L ≤ 64 * T ^ 2 := by
    apply (tableBudget_le n K L).trans
    gcongr
    dsimp [T]
    omega
  have hclear : entryPorts.length * (2 * B + 3) ≤ 1740 * T ^ 2 := by
    have h := Nat.mul_le_mul_right (2 * B + 3) entryPorts_length_le
    nlinarith
  dsimp only [commandBudget]
  change _ ≤ 1000000 * T ^ 2
  nlinarith

/-- Exact table output, runtime and every source prefix of the same closed
command. The relational literal contract is instantiated by the concrete
producer; it is not an extra premise of the final counting theorem. -/
theorem command_resources (a : OuterData) (B n K L : ℕ)
    (hb : ∀ i, (a.stacks i).length ≤ B)
    (hn : (staged a).stacks 552 = List.replicate n true)
    (h460 : (staged a).stacks 460 = []) (h573 : (staged a).stacks 573 = [])
    (h569 : (staged a).stacks 569 = []) (h561 : (staged a).stacks 561 = [])
    (h585 : (staged a).stacks 585 = [])
    (P : ℕ → List Bool → Prop)
    (hbody : RelLiteralBody (staged a).stacks literalIteration P K n L) :
    ∃ (payload : ℕ → List Bool) (steps : ℕ) (e : OuterData),
      (∀ j, j < n → (payload j).length ≤ L ∧ P j (payload j)) ∧
      steps ≤ commandBudget B n K L ∧
      Trace program steps (a.withPC (some program.entry)) (e.withPC none) ∧
      e.stacks 62 = tableResult payload n [] ∧
      (∀ i, i ∉ writtenPorts → e.stacks i = a.stacks i) ∧
      (∀ i ∈ writtenPorts, i≠62 → e.stacks i=[]) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 896 * B + commandBudget B n K L := by
  obtain ⟨payload, k, rf, hpayload, hk, he⟩ :=
    prepareFactor_rel_run (staged a).stacks P K n L hn h460 h573 h569 h561 h585 hbody
      (staged a).regs
  let middle : OuterData := ⟨rf, Function.update (staged a).stacks 561 (tableResult payload n [])⟩
  have hlen := rel_tableResult_length_le payload n L n le_rfl
    (fun i hi => (hpayload i hi).1) []
  simp only [List.length_nil, Nat.zero_add] at hlen
  have hmiddle : ∀ i, (middle.stacks i).length ≤ middleBound B n L := by
    intro i
    have hs := staged_stack_bound a B hb i
    by_cases hi : i = 561
    · subst i
      change (tableResult payload n []).length ≤ middleBound B n L
      dsimp only [middleBound]
      omega
    · change (Function.update (staged a).stacks 561 (tableResult payload n []) i).length ≤ _
      rw [Function.update_of_ne hi]
      dsimp only [middleBound]
      omega
  have hm62 : middle.stacks 62 = [] := by simpa [middle] using staged_output a
  have hmtmp : middle.stacks 684 = [] := by simpa [middle] using staged_temporary a
  have hrun := command_eval a middle k he hmtmp
  have hkc : k ≤ tableBudget n K L := by
    dsimp only [tableBudget, literalRecordBound] at hk ⊢
    nlinarith only [hk]
  have hclear := SubexpSetupStorage.clearManyCost_le entryPorts a B hb
  have hstage := stageCost_le a B hb
  have hexport := exportCost_le middle (middleBound B n L) hmiddle hm62
  have htotal : SubexpSetupStorage.clearManyCost entryPorts a +
      (stageCost a + (k + exportCost middle)) + 1 ≤ commandBudget B n K L := by
    dsimp only [commandBudget]
    omega
  refine ⟨payload, _, exported middle, hpayload, htotal,
    compiled_halt_trace hrun 556 62, ?_, ?_, ?_, ?_⟩
  · exact (exported_output middle hm62).trans (by simp [middle])
  · intro i hi
    exact command_output_frame a rf (tableResult payload n []) i hi
  · intro i hi hne
    exact command_output_clean a rf (tableResult payload n []) i hi hne
  · intro prefixSteps intermediate hp ht i
    exact StructuredSpace.local_stack_bound program (StreamResources.dataBits_le_mul _ hb)
      prefixSteps intermediate (hp.trans htotal) ht i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableSpace
