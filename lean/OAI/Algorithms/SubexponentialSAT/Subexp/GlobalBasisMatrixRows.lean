import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisRowStep

namespace OAI.Algorithms

/-! Counted ambient-row assembly from the actual packing lookup table.
Rows are visited in ascending index order; only the current row is prepared.
The final transfer reverses the accumulated scalar bytes once. -/

namespace SubexponentialSAT.Subexp.GlobalBasisProgram

open BitProgram StructuredCalls
open GlobalBasisInput (Context Location)

def matrixBits {p r Q Δ : ℕ} (C : Context p r Q Δ) (locs : List (Location r Q Δ))
    (xs : List GlobalBasisColumns.Descriptor) : List Bool :=
  locs.flatMap (fun loc => GlobalBasisRows.rowBits (C.row loc) xs)

def rowsBudget {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (xs : List GlobalBasisColumns.Descriptor) : ℕ → List (Location r Q Δ) → ℕ
  | _, [] => 2
  | i, loc :: rest => rowBudget C i loc xs + rowsBudget C xs (i+1) rest + 2

theorem stored_pop_rows {p r Q Δ : ℕ} [Fact p.Prime] {C : Context p r Q Δ} {d : Data}
    (hs : C.Stored d) : C.Stored (UnaryForPrograms.popped rowPorts d) := by
  constructor
  · simpa [UnaryForPrograms.popped, rowPorts] using hs.width
  · simpa [UnaryForPrograms.popped, rowPorts] using hs.zero
  · simpa [UnaryForPrograms.popped, rowPorts] using hs.one
  · simpa [UnaryForPrograms.popped, rowPorts] using hs.position
  · simpa [UnaryForPrograms.popped, rowPorts] using hs.metadata
  · simpa [UnaryForPrograms.popped, rowPorts] using hs.universal
  · simpa [UnaryForPrograms.popped, rowPorts] using hs.colors
  · simpa [UnaryForPrograms.popped, rowPorts] using hs.batch

theorem clean_pop_rows {d : Data} (hc : GlobalBasisRowPrepare.RowClean d) :
    GlobalBasisRowPrepare.RowClean (UnaryForPrograms.popped rowPorts d) := by
  intro i hi
  have h45 : i ≠ 45 := by
    intro he
    subst i
    change (45 < 12 ∨ (16 ≤ 45 ∧ 45 ≤ 31) ∨ 45 = 36 ∨ 45 = 41 ∨ 45 = 42 ∨ 45 = 43 ∨ 45 = 44) at hi
    omega
  simpa [UnaryForPrograms.popped, rowPorts, h45] using hc i hi

theorem rows_visits {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (xs : List GlobalBasisColumns.Descriptor) (locs : List (Location r Q Δ)) :
    ∀ index (d : Data), C.locations index locs → C.Stored d →
      GlobalBasisRowPrepare.RowClean d → d.stacks 34 = List.replicate index true →
      d.stacks 35 = Encoding.encodeList id (GlobalBasisRows.records xs) →
      d.stacks 45 = List.replicate locs.length true →
      (∀ loc ∈ locs, ∀ x ∈ xs, GlobalBasisEntry.Valid (C.row loc) x) →
      ∃ costs n e, n ≤ rowsBudget C xs index locs ∧
        UnaryForPrograms.Visits rowPorts rowStep costs n d e ∧
        e.stacks = Function.update (Function.update (Function.update d.stacks 45 []) 12
          ((matrixBits C locs xs).reverse ++ d.stacks 12))
            34 (List.replicate (index + locs.length) true) := by
  induction locs with
  | nil =>
    intro index d hm hs hc hi h35 h45 hv
    refine ⟨[], 2, UnaryForPrograms.popped rowPorts d, by rfl,
      .done d (by simpa [rowPorts] using h45), ?_⟩
    funext i
    by_cases h34 : i = 34 <;> by_cases h12 : i = 12 <;> by_cases h45' : i = 45 <;>
      simp_all [UnaryForPrograms.popped, rowPorts, matrixBits]
  | cons loc locs ih =>
    intro index d hm hs hc hi h35 h45 hv
    let a := UnaryForPrograms.popped rowPorts d
    have ha45 : a.stacks 45 = List.replicate locs.length true := by
      simp [a, UnaryForPrograms.popped, rowPorts, h45, List.replicate_succ]
    obtain ⟨n₁, b, hn₁, hb, hsb⟩ := rowStep_eval C index loc xs a hm.1
      (stored_pop_rows hs) (by simpa [a, UnaryForPrograms.popped, rowPorts] using hi)
      (clean_pop_rows hc) (by simpa [a, UnaryForPrograms.popped, rowPorts] using h35)
      (hv loc (by simp))
    have hbs : C.Stored b := stored_rowOutput (stored_pop_rows hs) _ _ hsb
    have hbc : GlobalBasisRowPrepare.RowClean b := clean_rowOutput (clean_pop_rows hc) _ _ hsb
    obtain ⟨costs, n₂, e, hn₂, he, hse⟩ := ih (index+1) b hm.2 hbs hbc
      (by simp [hsb]) (by simp [hsb, a, UnaryForPrograms.popped, rowPorts, h35])
      (by simpa [hsb] using ha45) (fun next hn => hv next (by simp [hn]))
    refine ⟨n₁ :: costs, n₁+n₂+2, e, ?_,
      .step (by simp [rowPorts, h45, List.replicate_succ]) hb
        (by simp [hsb, rowPorts, a]) he, ?_⟩
    · simp only [rowsBudget]
      omega
    · rw [hse, hsb]
      funext i
      by_cases h34 : i = 34 <;> by_cases h12 : i = 12 <;> by_cases h45' : i = 45 <;>
        simp_all [a, UnaryForPrograms.popped, rowPorts, matrixBits,
          List.reverse_append, List.append_assoc, Nat.add_assoc, Nat.add_comm]

theorem rows_eval {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (xs : List GlobalBasisColumns.Descriptor) (locs : List (Location r Q Δ))
    (index : ℕ) (d : Data) (hm : C.locations index locs) (hs : C.Stored d)
    (hc : GlobalBasisRowPrepare.RowClean d) (hi : d.stacks 34 = List.replicate index true)
    (h35 : d.stacks 35 = Encoding.encodeList id (GlobalBasisRows.records xs))
    (h45 : d.stacks 45 = List.replicate locs.length true)
    (hv : ∀ loc ∈ locs, ∀ x ∈ xs, GlobalBasisEntry.Valid (C.row loc) x) :
    ∃ n e, n ≤ rowsBudget C xs index locs ∧ Eval rows n d e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 45 []) 12
        ((matrixBits C locs xs).reverse ++ d.stacks 12))
          34 (List.replicate (index + locs.length) true) := by
  obtain ⟨costs, n, e, hn, he, hse⟩ := rows_visits C xs locs index d hm hs hc hi h35 h45 hv
  exact ⟨n, e, hn, he.eval, hse⟩

def matrixBudget {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (xs : List GlobalBasisColumns.Descriptor) (locs : List (Location r Q Δ)) : ℕ :=
  countBudget (GlobalBasisRows.records xs) + (7 * locs.length + 5) +
    rowsBudget C xs 0 locs + (2 * locs.length + 3) +
    (3 * (matrixBits C locs xs).length + 3)

theorem matrix_eval {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (xs : List GlobalBasisColumns.Descriptor) (locs : List (Location r Q Δ)) (d : Data)
    (hm : C.locations 0 locs) (hs : C.Stored d) (hc : GlobalBasisRowPrepare.RowClean d)
    (h12 : d.stacks 12 = []) (h34 : d.stacks 34 = [])
    (h35 : d.stacks 35 = Encoding.encodeList id (GlobalBasisRows.records xs))
    (h45 : d.stacks 45 = []) (h46 : d.stacks 46 = List.replicate locs.length true)
    (h50 : d.stacks 50 = []) (h51 : d.stacks 51 = [])
    (hv : ∀ loc ∈ locs, ∀ x ∈ xs, GlobalBasisEntry.Valid (C.row loc) x) :
    ∃ n e, n ≤ matrixBudget C xs locs ∧ Eval matrix n d e ∧
      e.stacks = Function.update (Function.update d.stacks 50 (List.replicate xs.length true))
        51 (matrixBits C locs xs) := by
  obtain ⟨a, ha, hsa⟩ := countColumns_eval (GlobalBasisRows.records xs) d h35
    (hc 16 (by decide)) (hc 31 (by decide)) h50
  let b := copied 46 45 a
  have hb := copy_eval 46 45 a (by decide) (by decide) (by decide) (by simp [hsa, hc 31 (by decide)])
  have hbs : b.stacks = Function.update (Function.update d.stacks 50 (List.replicate xs.length true))
      45 (List.replicate locs.length true) := by
    simp [b, copied, StackRoutines.copyStacks, hsa, GlobalBasisRows.records, h45, h46]
  have hstored : C.Stored b := by
    constructor
    · simpa [hbs] using hs.width
    · simpa [hbs] using hs.zero
    · simpa [hbs] using hs.one
    · simpa [hbs] using hs.position
    · simpa [hbs] using hs.metadata
    · simpa [hbs] using hs.universal
    · simpa [hbs] using hs.colors
    · simpa [hbs] using hs.batch
  have hclean : GlobalBasisRowPrepare.RowClean b := by
    intro i hi
    have hi45 : i ≠ 45 := by
      intro he; subst i
      change (45 < 12 ∨ (16 ≤ 45 ∧ 45 ≤ 31) ∨ 45 = 36 ∨ 45 = 41 ∨ 45 = 42 ∨ 45 = 43 ∨ 45 = 44) at hi
      omega
    have hi50 : i ≠ 50 := by
      intro he; subst i
      change (50 < 12 ∨ (16 ≤ 50 ∧ 50 ≤ 31) ∨ 50 = 36 ∨ 50 = 41 ∨ 50 = 42 ∨ 50 = 43 ∨ 50 = 44) at hi
      omega
    simpa [hbs, hi45, hi50] using hc i hi
  obtain ⟨m, c, hm', hrows, hsc⟩ := rows_eval C xs locs 0 b hm hstored hclean
    (by simp [hbs, h34]) (by simp [hbs, h35]) (by simp [hbs]) hv
  let f := cleared 34 c
  let e := transferred 12 51 f
  have hf := clear_eval 34 c
  have he := transfer_eval 12 51 f (by decide)
  have ha46 : a.stacks 46 = List.replicate locs.length true := by simp [hsa, h46]
  have hc34 : (c.stacks 34).length = locs.length := by simp [hsc]
  have hf12 : (f.stacks 12).length = (matrixBits C locs xs).length := by
    simp [f, cleared, hsc, hbs, h12]
  have hall := ha.seq (hb.seq (hrows.seq (hf.seq (he.seq (.base (.skip e))))))
  rw [ha46] at hall
  simp only [List.length_replicate] at hall
  refine ⟨_, e, ?_, by simpa only [matrix, sequence, List.foldr, Nat.add_zero] using hall, ?_⟩
  · rw [hc34, hf12]
    unfold matrixBudget
    omega
  · funext i
    by_cases hi12 : i = 12 <;> by_cases hi34 : i = 34 <;> by_cases hi45 : i = 45 <;>
      by_cases hi50 : i = 50 <;> by_cases hi51 : i = 51 <;>
      simp_all [e, transferred, f, cleared, StackRoutines.transferStacks]

end SubexponentialSAT.Subexp.GlobalBasisProgram

end OAI.Algorithms
