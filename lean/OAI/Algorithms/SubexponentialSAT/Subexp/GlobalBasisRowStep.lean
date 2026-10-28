import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisProgramSupport
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisInput

namespace OAI.Algorithms

/-! The actual native row step: prepare metadata, copy only the descriptor
stream, evaluate its entries, clear the row fields, and increment the row
index. Existing matrix output and all shared input masters are framed. -/

namespace SubexponentialSAT.Subexp.GlobalBasisProgram

open BitProgram StructuredCalls
open GlobalBasisInput (Context Location)

theorem ready_copy_descriptors {p : ℕ} [Fact p.Prime] (R : GlobalBasisEntry.Row p) (d : Data)
    (H : GlobalBasisRows.Invariant R (projectState id low32 d)) :
    GlobalBasisRows.Invariant R (projectState id low32 (copied 35 6 d)) := by
  rcases H with ⟨H, H8, H9, H10⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · simpa [projectState, low32, copied, StackRoutines.copyStacks] using H.table
    · simpa [projectState, low32, copied, StackRoutines.copyStacks] using H.dimension
    · simpa [projectState, low32, copied, StackRoutines.copyStacks] using H.coordinate
    · simpa [projectState, low32, copied, StackRoutines.copyStacks] using H.block
    · simpa [projectState, low32, copied, StackRoutines.copyStacks] using H.color
    · simpa [projectState, low32, copied, StackRoutines.copyStacks] using H.rank
    · simpa [projectState, low32, copied, StackRoutines.copyStacks] using H.width
    · simpa [projectState, low32, copied, StackRoutines.copyStacks] using H.zero
    · simpa [projectState, low32, copied, StackRoutines.copyStacks] using H.one
    · simpa [projectState, copied, readRegs] using H.kind
    · simpa [projectState, low32, copied, StackRoutines.copyStacks] using H.output
    · intro i hi
      have h6 : low32 i ≠ 6 := by
        intro h
        have hh := congrArg Fin.val h
        change i.val = 6 at hh
        omega
      simpa [projectState, copied, StackRoutines.copyStacks, h6] using H.work i hi
  · simpa [projectState, low32, copied, StackRoutines.copyStacks] using H8
  · simpa [projectState, low32, copied, StackRoutines.copyStacks] using H9
  · simpa [projectState, low32, copied, StackRoutines.copyStacks] using H10

def rowDataSize {p : ℕ} [Fact p.Prime] (R : GlobalBasisEntry.Row p) : ℕ :=
  (BasisTransposeProgram.rows (MatrixWordEncoding.code p) R.table).flatten.length +
    R.N + R.coordinate + R.block + R.color + R.rank

def rowBudget {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (index : ℕ) (loc : Location r Q Δ) (xs : List GlobalBasisColumns.Descriptor) : ℕ :=
  C.setupBudget index loc + 7 * GlobalBasisRows.encodedSize xs + 5 +
    2000 * (GlobalBasisRows.baseSize (C.row loc) + GlobalBasisRows.encodedSize xs + 1)^4 +
    (2 * rowDataSize (C.row loc) + 18) + 2

theorem rowStep_eval {p r Q Δ : ℕ} [Fact p.Prime] (C : Context p r Q Δ)
    (index : ℕ) (loc : Location r Q Δ) (xs : List GlobalBasisColumns.Descriptor) (d : Data)
    (hm : C.matches index loc) (hs : C.Stored d)
    (hi : d.stacks 34 = List.replicate index true)
    (hc : GlobalBasisRowPrepare.RowClean d)
    (h35 : d.stacks 35 = Encoding.encodeList id (GlobalBasisRows.records xs))
    (hv : ∀ x ∈ xs, GlobalBasisEntry.Valid (C.row loc) x) :
    ∃ n e, n ≤ rowBudget C index loc xs ∧ Eval rowStep n d e ∧
      e.stacks = Function.update (Function.update d.stacks 12
        ((GlobalBasisRows.rowBits (C.row loc) xs).reverse ++ d.stacks 12))
          34 (List.replicate (index+1) true) := by
  obtain ⟨b, ⟨n₁, hn₁, hb⟩, hsb, hready⟩ := C.prepare index loc d hm hs hi hc
  have hb' : Eval (.call GlobalBasisRowPrepare.program) n₁ d b := .call _ hb
  have hb31 : b.stacks 31 = [] := by
    rw [hsb, GlobalBasisRowPrepare.rowStacks_frame (C.row loc) d.stacks 31 (by decide)]
    exact hc 31 (by decide)
  let a := copied 35 6 b
  have ha := copy_eval 35 6 b (by decide) (by decide) (by decide) hb31
  have hready' : GlobalBasisRows.Invariant (C.row loc) (projectState id low32 a) :=
    ready_copy_descriptors (C.row loc) b hready
  have hb6 : b.stacks 6 = [] := by
    rw [hsb, GlobalBasisRowPrepare.rowStacks_frame (C.row loc) d.stacks 6 (by decide)]
    exact hc 6 (by decide)
  have hb35 : b.stacks 35 = Encoding.encodeList id (GlobalBasisRows.records xs) := by
    rw [hsb, GlobalBasisRowPrepare.rowStacks_frame (C.row loc) d.stacks 35 (by decide)]
    exact h35
  have ha6 : a.stacks 6 = Encoding.encodeList id (GlobalBasisRows.records xs) := by
    simp [a, copied, StackRoutines.copyStacks, hb6, hb35]
  have ha7 : a.stacks 7 = [] := by
    simp only [a, copied, StackRoutines.copyStacks, Function.update_of_ne (by decide : (7 : Fin 64) ≠ 6)]
    rw [hsb, GlobalBasisRowPrepare.rowStacks_frame (C.row loc) d.stacks 7 (by decide)]
    exact hc 7 (by decide)
  obtain ⟨n₂, f, hn₂, hf, hsf⟩ := row_eval (C.row loc) xs a hready' hv ha6 ha7
  have hf' : f.stacks = Function.update (GlobalBasisRowPrepare.rowStacks (C.row loc) d.stacks) 12
      ((GlobalBasisRows.rowBits (C.row loc) xs).reverse ++ d.stacks 12) := by
    rw [hsf]
    funext i
    by_cases hi6 : i = 6
    · subst i
      simp [GlobalBasisRowPrepare.rowStacks_frame (C.row loc) d.stacks 6 (by decide), hc 6 (by decide)]
    · by_cases hi12 : i = 12
      · subst i
        simp [a, copied, StackRoutines.copyStacks, hsb,
          GlobalBasisRowPrepare.rowStacks_frame (C.row loc) d.stacks 12 (by decide)]
      · simp [a, copied, StackRoutines.copyStacks, hsb, hi6, hi12]
  obtain ⟨n₃, g, hn₃, hg, hsg⟩ := clearList_eval [0,1,2,3,4,5] f
  have hg' : g.stacks = Function.update d.stacks 12
      ((GlobalBasisRows.rowBits (C.row loc) xs).reverse ++ d.stacks 12) := by
    rw [hsg, hf']
    funext i
    fin_cases i <;> simp [GlobalBasisRowPrepare.rowStacks,
      hc 0 (by decide), hc 1 (by decide), hc 2 (by decide), hc 3 (by decide),
      hc 4 (by decide), hc 5 (by decide)]
  have hclear : clearBudget [0,1,2,3,4,5] f.stacks = 2 * rowDataSize (C.row loc) + 18 := by
    simp [clearBudget, hf', GlobalBasisRowPrepare.rowStacks, rowDataSize]
    omega
  let e := TupleProgram.pushedState 34 0 true g
  have he := hb'.seq (ha.seq (hf.seq (hg.seq ((push_eval 34 true g).seq (.base (.skip e))))))
  rw [hb35] at he
  refine ⟨_, e, ?_, by simpa only [rowStep, sequence, List.foldr, Nat.add_zero] using he, ?_⟩
  · rw [hclear] at hn₃
    unfold GlobalBasisRows.encodedSize at hn₂
    unfold rowBudget GlobalBasisRows.encodedSize
    omega
  · simp [e, hg', hi, List.replicate_succ]

theorem stored_rowOutput {p r Q Δ : ℕ} [Fact p.Prime] {C : Context p r Q Δ} {d e : Data}
    (h : C.Stored d) (bits index : List Bool)
    (hs : e.stacks = Function.update (Function.update d.stacks 12 bits) 34 index) : C.Stored e := by
  constructor
  · simpa [hs] using h.width
  · simpa [hs] using h.zero
  · simpa [hs] using h.one
  · simpa [hs] using h.position
  · simpa [hs] using h.metadata
  · simpa [hs] using h.universal
  · simpa [hs] using h.colors
  · simpa [hs] using h.batch

theorem clean_rowOutput {d e : Data} (h : GlobalBasisRowPrepare.RowClean d)
    (bits index : List Bool)
    (hs : e.stacks = Function.update (Function.update d.stacks 12 bits) 34 index) :
    GlobalBasisRowPrepare.RowClean e := by
  intro i hi
  have h12 : i ≠ 12 := by
    intro he
    subst i
    change (12 < 12 ∨ (16 ≤ 12 ∧ 12 ≤ 31) ∨ 12 = 36 ∨ 12 = 41 ∨ 12 = 42 ∨ 12 = 43 ∨ 12 = 44) at hi
    omega
  have h34 : i ≠ 34 := by
    intro he
    subst i
    change (34 < 12 ∨ (16 ≤ 34 ∧ 34 ≤ 31) ∨ 34 = 36 ∨ 34 = 41 ∨ 34 = 42 ∨ 34 = 43 ∨ 34 = 44) at hi
    omega
  simpa [hs, h12, h34] using h i hi

end SubexponentialSAT.Subexp.GlobalBasisProgram

end OAI.Algorithms
