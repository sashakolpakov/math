import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMatrixRows
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisPrepareColumns
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisMatrixOutput

namespace OAI.Algorithms

/-! Complete matrix phases of the fixed global basis assembler. -/

namespace SubexponentialSAT.Subexp.GlobalBasisProgram

open BitProgram StructuredCalls
open GlobalBasisInput (Context Location)

def retainedPorts : List (Fin 64) :=
  [13,14,15,32,33,37,38,39,40,46,47,48,49,55,63]

def WorkClean (d : Data) : Prop := ∀ i, i ∉ retainedPorts → d.stacks i = []

theorem WorkClean.row {d : Data} (h : WorkClean d) : GlobalBasisRowPrepare.RowClean d := by
  intro i hi
  apply h i
  intro hm
  simp only [retainedPorts, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [Fin.coe_ofNat_eq_mod] at hi

theorem WorkClean.inner {d : Data} (h : WorkClean d) : InnerClean d := by
  intro i hi
  apply h i
  have hd : ∀ j : Fin 64, j ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
      16, 17, 18, 19, 20, 21, 22, 31, 35] → j ∉ retainedPorts := by decide
  exact hd i hi

theorem WorkClean.outer {d : Data} (h : WorkClean d) : OuterClean d := by
  intro i hi
  apply h i
  have hd : ∀ j : Fin 64, j ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11,
      16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 31, 35] → j ∉ retainedPorts := by decide
  exact hd i hi

theorem stored_descriptors {p r Q Δ : ℕ} [Fact p.Prime] {C : Context p r Q Δ}
    {d a : Data} (hs : C.Stored d) (bits : List Bool)
    (ha : a.stacks = Function.update d.stacks 35 bits) : C.Stored a := by
  constructor
  · simpa [ha] using hs.width
  · simpa [ha] using hs.zero
  · simpa [ha] using hs.one
  · simpa [ha] using hs.position
  · simpa [ha] using hs.metadata
  · simpa [ha] using hs.universal
  · simpa [ha] using hs.colors
  · simpa [ha] using hs.batch

theorem clean_descriptors {d a : Data} (hs : GlobalBasisRowPrepare.RowClean d) (bits : List Bool)
    (ha : a.stacks = Function.update d.stacks 35 bits) : GlobalBasisRowPrepare.RowClean a := by
  intro i hi
  have h35 : i ≠ 35 := by
    intro he; subst i
    change (35 < 12 ∨ (16 ≤ 35 ∧ 35 ≤ 31) ∨ 35 = 36 ∨ 35 = 41 ∨ 35 = 42 ∨ 35 = 43 ∨ 35 = 44) at hi
    omega
  simpa [ha, h35] using hs i hi

def innerColumns {p r Q Δ : ℕ} (C : Context p r Q Δ) (count : ℕ) (g : Fin r) :=
  innerDescriptors count g.val (C.tables g).split

def outerColumnsList {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ) (count leftovers : ℕ) :=
  outerDescriptors count leftovers C.data

def innerRecord {p r Q Δ : ℕ} (C : Context p r Q Δ) (count : ℕ)
    (locs : List (Location r Q Δ)) (g : Fin r) : List Bool :=
  GlobalBasisMatrixOutput.record (List.replicate (innerColumns C count g).length true)
    (matrixBits C locs (innerColumns C count g))

def outerRecord {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ) (count leftovers : ℕ)
    (locs : List (Location r Q Δ)) : List Bool :=
  GlobalBasisMatrixOutput.record (List.replicate (outerColumnsList C count leftovers).length true)
    (matrixBits C locs (outerColumnsList C count leftovers))

def innerStepBudget {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ) (count : ℕ)
    (locs : List (Location r Q Δ)) (g : Fin r) : ℕ :=
  innerBudget C.batch.length count g.val (C.tables g).dimension (C.tables g).split (C.tables g).bits.length +
    matrixBudget C (innerColumns C count g) locs +
    GlobalBasisMatrixOutput.cost (List.replicate (innerColumns C count g).length true)
      (matrixBits C locs (innerColumns C count g))
      (Encoding.encodeList id (GlobalBasisRows.records (innerColumns C count g)))

def outerPhaseBudget {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ) (count leftovers : ℕ)
    (locs : List (Location r Q Δ)) : ℕ :=
  outerBudget count leftovers C.data + matrixBudget C (outerColumnsList C count leftovers) locs +
    GlobalBasisMatrixOutput.cost (List.replicate (outerColumnsList C count leftovers).length true)
      (matrixBits C locs (outerColumnsList C count leftovers))
      (Encoding.encodeList id (GlobalBasisRows.records (outerColumnsList C count leftovers)))

theorem innerStep_eval {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ) (count : ℕ)
    (locs : List (Location r Q Δ)) (g : Fin r) (d : Data)
    (hm : C.locations 0 locs) (hs : C.Stored d) (hc : WorkClean d)
    (h46 : d.stacks 46 = List.replicate locs.length true)
    (h48 : d.stacks 48 = List.replicate count true)
    (h55 : d.stacks 55 = List.replicate g.val true)
    (hv : ∀ loc ∈ locs, ∀ x ∈ innerColumns C count g, GlobalBasisEntry.Valid (C.row loc) x) :
    ∃ n e, n ≤ innerStepBudget C count locs g ∧ Eval innerStep n d e ∧
      e.stacks = Function.update d.stacks 63 (innerRecord C count locs g ++ d.stacks 63) := by
  obtain ⟨n₁, a, hn₁, ha, hsa⟩ := prepareInner_eval (C.before g) (C.tables g).dimension
    (C.tables g).split count (C.tables g).bits (C.after g) d
    (hs.batch.trans (C.batch_split g)) (by simpa [C.before_length g, GlobalBasisRecordLookup.unary] using h55)
    h48 hc.inner
  have hsa' : a.stacks = Function.update d.stacks 35
      (Encoding.encodeList id (GlobalBasisRows.records (innerColumns C count g))) := by
    simpa [innerColumns, C.before_length g, innerDescriptors_encode] using hsa
  obtain ⟨n₂, b, hn₂, hb, hsb⟩ := matrix_eval C (innerColumns C count g) locs a hm
    (stored_descriptors hs _ hsa') (clean_descriptors hc.row _ hsa')
    (by simp [hsa', hc 12 (by decide)]) (by simp [hsa', hc 34 (by decide)])
    (by simp [hsa']) (by simp [hsa', hc 45 (by decide)])
    (by simp [hsa', h46]) (by simp [hsa', hc 50 (by decide)])
    (by simp [hsa', hc 51 (by decide)]) hv
  obtain ⟨e, he, hse⟩ := GlobalBasisMatrixOutput.command_eval
    (List.replicate (innerColumns C count g).length true) (matrixBits C locs (innerColumns C count g)) b
    (by simp [hsb]) (by simp [hsb]) (by simp [hsb, hsa', hc 31 (by decide)])
    (by simp [hsb, hsa', hc 56 (by decide)]) (by simp [hsb, hsa', hc 57 (by decide)])
    (by simp [hsb, hsa', hc 58 (by decide)])
  have hb35 : b.stacks 35 = Encoding.encodeList id (GlobalBasisRows.records (innerColumns C count g)) := by
    simp [hsb, hsa']
  have hall := ha.seq (hb.seq (he.seq (.base (.skip e))))
  rw [hb35] at hall
  refine ⟨_, e, ?_, by simpa only [innerStep, sequence, List.foldr, Nat.add_zero] using hall, ?_⟩
  · rw [hs.batch, C.before_length g] at hn₁
    unfold innerStepBudget
    omega
  · rw [hse, hsb, hsa']
    funext i
    by_cases h35 : i = 35
    · subst i; simp [GlobalBasisMatrixOutput.resultStacks, hc 35 (by decide)]
    by_cases h50 : i = 50
    · subst i; simp [GlobalBasisMatrixOutput.resultStacks, hc 50 (by decide)]
    by_cases h51 : i = 51
    · subst i; simp [GlobalBasisMatrixOutput.resultStacks, hc 51 (by decide)]
    by_cases h63 : i = 63
    · subst i; simp [GlobalBasisMatrixOutput.resultStacks, innerRecord]
    · simp [GlobalBasisMatrixOutput.resultStacks, h35, h50, h51, h63]

theorem outerPhase_eval {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (count leftovers : ℕ) (locs : List (Location r Q Δ)) (d : Data)
    (hm : C.locations 0 locs) (hs : C.Stored d) (hc : WorkClean d)
    (h46 : d.stacks 46 = List.replicate locs.length true)
    (h48 : d.stacks 48 = List.replicate count true)
    (h49 : d.stacks 49 = List.replicate leftovers true)
    (hv : ∀ loc ∈ locs, ∀ x ∈ outerColumnsList C count leftovers, GlobalBasisEntry.Valid (C.row loc) x) :
    ∃ n e, n ≤ outerPhaseBudget C count leftovers locs ∧
      Eval (sequence [prepareOuter, matrix, emitMatrix]) n d e ∧
      e.stacks = Function.update d.stacks 63 (outerRecord C count leftovers locs ++ d.stacks 63) := by
  obtain ⟨n₁, a, hn₁, ha, hsa⟩ := prepareOuter_eval count leftovers C.data d hs.batch
    (by simpa [GlobalBasisInput.Context.data] using hs.colors) h48 h49 hc.outer
  have hsa' : a.stacks = Function.update d.stacks 35
      (Encoding.encodeList id (GlobalBasisRows.records (outerColumnsList C count leftovers))) := by
    simpa [outerColumnsList, outerDescriptors_encode] using hsa
  obtain ⟨n₂, b, hn₂, hb, hsb⟩ := matrix_eval C (outerColumnsList C count leftovers) locs a hm
    (stored_descriptors hs _ hsa') (clean_descriptors hc.row _ hsa')
    (by simp [hsa', hc 12 (by decide)]) (by simp [hsa', hc 34 (by decide)])
    (by simp [hsa']) (by simp [hsa', hc 45 (by decide)])
    (by simp [hsa', h46]) (by simp [hsa', hc 50 (by decide)])
    (by simp [hsa', hc 51 (by decide)]) hv
  obtain ⟨e, he, hse⟩ := GlobalBasisMatrixOutput.command_eval
    (List.replicate (outerColumnsList C count leftovers).length true)
    (matrixBits C locs (outerColumnsList C count leftovers)) b
    (by simp [hsb]) (by simp [hsb]) (by simp [hsb, hsa', hc 31 (by decide)])
    (by simp [hsb, hsa', hc 56 (by decide)]) (by simp [hsb, hsa', hc 57 (by decide)])
    (by simp [hsb, hsa', hc 58 (by decide)])
  have hb35 : b.stacks 35 = Encoding.encodeList id (GlobalBasisRows.records (outerColumnsList C count leftovers)) := by
    simp [hsb, hsa']
  have hall := ha.seq (hb.seq (he.seq (.base (.skip e))))
  rw [hb35] at hall
  refine ⟨_, e, ?_, by simpa only [sequence, List.foldr, Nat.add_zero] using hall, ?_⟩
  · unfold outerPhaseBudget
    omega
  · rw [hse, hsb, hsa']
    funext i
    by_cases h35 : i = 35
    · subst i; simp [GlobalBasisMatrixOutput.resultStacks, hc 35 (by decide)]
    by_cases h50 : i = 50
    · subst i; simp [GlobalBasisMatrixOutput.resultStacks, hc 50 (by decide)]
    by_cases h51 : i = 51
    · subst i; simp [GlobalBasisMatrixOutput.resultStacks, hc 51 (by decide)]
    by_cases h63 : i = 63
    · subst i; simp [GlobalBasisMatrixOutput.resultStacks, outerRecord]
    · simp [GlobalBasisMatrixOutput.resultStacks, h35, h50, h51, h63]

end SubexponentialSAT.Subexp.GlobalBasisProgram

end OAI.Algorithms
