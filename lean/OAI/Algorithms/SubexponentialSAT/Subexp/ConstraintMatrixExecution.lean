import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixCalls

namespace OAI.Algorithms

/-! Actual construction of the complete local defect matrix from the Side
records, with the Joint records generated inside the fixed slot loop. -/

namespace SubexponentialSAT.Subexp.ConstraintMatrixProgram

open BitProgram StructuredCalls MatrixWordEncoding MulticolorTypes

variable {r Q Δ : ℕ}

noncomputable def columns (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    List (UniversalType r Q Δ) := (TypeEnumeration.sideList hr hQ t g).map Subtype.val

noncomputable def rows (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    List (UniversalType r Q Δ) := (TypeEnumeration.jointList hr hQ t g i).map Subtype.val

theorem columns_bytes (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    (columns (Δ := Δ) hr hQ t g).map CollisionProgram.encodeType =
      TypeEnumeration.sideBytes r Q Δ t.val g.val := by
  simpa only [columns, List.map_map, Function.comp_def] using TypeEnumeration.sideList_bytes hr hQ t g

theorem rows_bytes (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) (i : Fin Δ) :
    (rows hr hQ t g i).map CollisionProgram.encodeType =
      TypeEnumeration.jointBytes r Q Δ t.val g.val i.val := by
  simpa only [rows, List.map_map, Function.comp_def] using TypeEnumeration.jointList_bytes hr hQ t g i

def anchor (g : Fin r) : UniversalType r Q Δ := ⟨fun _ => g, fun _ _ => g⟩

noncomputable def blocks (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) (i : Fin Δ) : List Bool :=
  ConstraintMatrixSlot.rowsBytes p i t coefficients (rows hr hQ t g i) (columns hr hQ t g)

noncomputable def rowCounts (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r)
    (i : Fin Δ) : List Bool := List.replicate (rows hr hQ t g i).length true

noncomputable def matrixBytes (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) : List Bool :=
  (List.ofFn (blocks (Δ := Δ) p hr hQ t g coefficients)).flatten

noncomputable def rowCount (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) : ℕ :=
  (List.ofFn fun i : Fin Δ => (rows hr hQ t g i).length).sum

theorem flatten_replicates (ns : List ℕ) :
    (ns.map (fun n => List.replicate n true)).flatten = List.replicate ns.sum true := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
      simp only [List.map_cons, List.flatten_cons, List.sum_cons]
      rw [ih, List.replicate_add]

theorem rowCounts_all (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) :
    emittedPrefix (rowCounts (Δ := Δ) hr hQ t g) Δ = List.replicate (rowCount (Δ := Δ) hr hQ t g) true := by
  rw [prefix_all]
  change (List.ofFn (fun i : Fin Δ => List.replicate (rows hr hQ t g i).length true)).flatten =
    List.replicate (List.ofFn (fun i : Fin Δ => (rows hr hQ t g i).length)).sum true
  simpa only [List.map_ofFn, Function.comp_def] using
    flatten_replicates (List.ofFn fun i : Fin Δ => (rows hr hQ t g i).length)

def Invariant (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) (k : ℕ) (a : Data) : Prop :=
  k ≤ Δ ∧ ∃ regs remaining,
    a = state p r Q t.val g.val coefficients (TypeEnumeration.sideBytes r Q Δ t.val g.val)
      regs k [] (emittedPrefix (blocks (Δ := Δ) p hr hQ t g coefficients) k).reverse
      (emittedPrefix (rowCounts (Δ := Δ) hr hQ t g) k).reverse remaining

theorem invariant_stable (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) :
    UnaryForPrograms.FrameStable loopPorts (Invariant (Δ := Δ) p hr hQ t g coefficients) := by
  intro k a b hf ha
  obtain ⟨hk, regs, remaining, rfl⟩ := ha
  refine ⟨hk, b.regs, b.stacks 64, ?_⟩
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    by_cases hj : j = 64
    · subst j; simp
    · have h := hf j (by simpa [loopPorts] using hj)
      simpa [state, hj] using h.symm

noncomputable def slotCost (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (E : ℕ) (i : Fin Δ) : ℕ :=
  TypeFiberProgram.budget true ⟨r, t.val, g.val, Q * r, i.val⟩
    (TypeEnumeration.sideBytes r Q Δ t.val g.val) +
  ConstraintMatrixSlot.budget p E (columns (Δ := Δ) hr hQ t g).length
    (ProgramEncoding.encodeRecords (TypeEnumeration.sideBytes r Q Δ t.val g.val)).length
    (rows hr hQ t g i).length r Q Δ + 4

noncomputable def loopCost (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (E k : ℕ) : ℕ :=
  if h : k < Δ then slotCost p hr hQ t g E ⟨k, h⟩ else 0

theorem body_spec (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p))
    (E : ℕ) (hE : ∀ i : Fin Δ, ∀ u ∈ rows hr hQ t g i, ∀ y ∈ columns hr hQ t g,
      ConstraintEntryProgram.programBudget p i t u y coefficients ≤ E) :
    ConstraintMatrixFor.BodyStep loopPorts body Δ (Invariant (Δ := Δ) p hr hQ t g coefficients)
      (loopCost (Δ := Δ) p hr hQ t g E) := by
  intro k hk a ha
  obtain ⟨_, regs, remaining, rfl⟩ := ha
  let i : Fin Δ := ⟨k, hk⟩
  let acc := (emittedPrefix (blocks (Δ := Δ) p hr hQ t g coefficients) k).reverse
  let count := (emittedPrefix (rowCounts (Δ := Δ) hr hQ t g) k).reverse
  obtain ⟨nf, hnf, fr, hf⟩ := joint_eval p r Q Δ t.val g.val k coefficients regs acc count remaining
  obtain ⟨ns, hns, sr, hs⟩ := slot_eval p h2 i t g (anchor g) coefficients
    (rows hr hQ t g i) (columns hr hQ t g) E (hE i) fr acc count remaining
  rw [columns_bytes, rows_bytes] at hs
  let nextAcc := (blocks (Δ := Δ) p hr hQ t g coefficients i).reverse ++ acc
  let nextCount := rowCounts (Δ := Δ) hr hQ t g i ++ count
  have hs' : Eval emitSlot ns
      (state p r Q t.val g.val coefficients (TypeEnumeration.sideBytes r Q Δ t.val g.val)
        fr k (ProgramEncoding.encodeRecords (TypeEnumeration.jointBytes r Q Δ t.val g.val k))
        acc count remaining)
      (state p r Q t.val g.val coefficients (TypeEnumeration.sideBytes r Q Δ t.val g.val)
        sr k [] nextAcc nextCount remaining) := hs
  have ht := advance_eval p r Q t.val g.val coefficients
    (TypeEnumeration.sideBytes r Q Δ t.val g.val) sr k [] nextAcc nextCount remaining
  let final := state p r Q t.val g.val coefficients (TypeEnumeration.sideBytes r Q Δ t.val g.val)
    (Function.update sr 0 true) (k + 1) [] nextAcc nextCount remaining
  have hacc : nextAcc = (emittedPrefix (blocks (Δ := Δ) p hr hQ t g coefficients) (k + 1)).reverse := by
    rw [show k + 1 = i.val + 1 from rfl, prefix_step]
    simp [nextAcc, acc, i]
  have hcount : nextCount = (emittedPrefix (rowCounts (Δ := Δ) hr hQ t g) (k + 1)).reverse := by
    rw [show k + 1 = i.val + 1 from rfl, prefix_step]
    simp [nextCount, count, rowCounts, i]
  refine ⟨nf + (ns + 4), final, ?_, hf.seq (hs'.seq ht), ?_, ?_⟩
  · simp only [loopCost, dite_eq_left hk, slotCost]
    rw [columns_bytes] at hns
    dsimp only [i] at hns
    omega
  · simp [final, state, loopPorts]
  · exact ⟨by omega, Function.update sr 0 true, remaining, by simp only [final, hacc, hcount]⟩

noncomputable def budget (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) (E : ℕ) : ℕ :=
  CounterForPrograms.budgetSum (loopCost (Δ := Δ) p hr hQ t g E) 0 Δ +
    2 * Δ + 3 * (matrixBytes (Δ := Δ) p hr hQ t g coefficients).length + 8

noncomputable def output (p : ℕ) [Fact p.Prime] (hr : 0 < r) (hQ : 0 < Q)
    (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p)) (regs : Fin 18 → Bool) : Data :=
  ⟨regs, Function.update
    (state p r Q t.val g.val coefficients (TypeEnumeration.sideBytes r Q Δ t.val g.val)
      regs Δ [] [] (List.replicate (rowCount (Δ := Δ) hr hQ t g) true) []).stacks
    0 (matrixBytes (Δ := Δ) p hr hQ t g coefficients)⟩

theorem program_runsIn (p : ℕ) [Fact p.Prime] (h2 : (2 : ZMod p) ≠ 0)
    (hr : 0 < r) (hQ : 0 < Q) (t : Fin Q) (g : Fin r) (coefficients : List (ZMod p))
    (E : ℕ) (hE : ∀ i : Fin Δ, ∀ u ∈ rows hr hQ t g i, ∀ y ∈ columns hr hQ t g,
      ConstraintEntryProgram.programBudget p i t u y coefficients ≤ E)
    (regs : Fin 18 → Bool) :
    ∃ out, RunsIn program (budget (Δ := Δ) p hr hQ t g coefficients E)
      ((input p r Q Δ t.val g.val coefficients (TypeEnumeration.sideBytes r Q Δ t.val g.val)
        regs).withPC (some program.entry))
      ((output (Δ := Δ) p hr hQ t g coefficients out).withPC none) := by
  let start := input p r Q Δ t.val g.val coefficients (TypeEnumeration.sideBytes r Q Δ t.val g.val) regs
  let a := state p r Q t.val g.val coefficients (TypeEnumeration.sideBytes r Q Δ t.val g.val)
    (Function.update regs 0 true) 0 [] [] [] (List.replicate Δ true)
  have hi : Invariant (Δ := Δ) p hr hQ t g coefficients 0 a :=
    ⟨Nat.zero_le _, Function.update regs 0 true, List.replicate Δ true, by simp [a]⟩
  have hn : (a.stacks loopPorts.counter).length = Δ := by simp [a, state, loopPorts]
  obtain ⟨costs, n, b, _, he, hb, hempty, _, htime, hcost⟩ := ConstraintMatrixFor.for_correct
    loopPorts body Δ (Invariant (Δ := Δ) p hr hQ t g coefficients) (loopCost (Δ := Δ) p hr hQ t g E)
    (invariant_stable p hr hQ t g coefficients) (body_spec p h2 hr hQ t g coefficients E hE) a hn hi
  obtain ⟨_, br, remaining, rfl⟩ := hb
  have hrem : remaining = [] := by simpa [state, loopPorts] using hempty
  subst remaining
  let matrix := matrixBytes (Δ := Δ) p hr hQ t g coefficients
  let b := state p r Q t.val g.val coefficients (TypeEnumeration.sideBytes r Q Δ t.val g.val)
    br Δ [] matrix.reverse (List.replicate (rowCount (Δ := Δ) hr hQ t g) true) []
  have hcounts : (List.ofFn (rowCounts (Δ := Δ) hr hQ t g)).flatten =
      List.replicate (rowCount (Δ := Δ) hr hQ t g) true := by
    simpa only [prefix_all] using rowCounts_all (Δ := Δ) hr hQ t g
  have he' : Eval (UnaryForPrograms.forCmd loopPorts body) n a b := by
    simpa only [b, matrix, prefix_all, hcounts, List.reverse_replicate, matrixBytes] using he
  have tf := TupleProgram.transfer_eval (50 : Fin 65) 0 (16 : Fin 18) 17
    (by decide) (by decide) b
  let out := readRegs br 16 17 none
  have hf : (⟨out, StackRoutines.transferStacks 50 0 b.stacks⟩ : Data) =
      output (Δ := Δ) p hr hQ t g coefficients out := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      by_cases h0 : j = 0
      · subst j; simp [b, state, StackRoutines.transferStacks, matrix]
      by_cases h50 : j = 50
      · subst j; simp [b, state, StackRoutines.transferStacks]
      simp [b, state, StackRoutines.transferStacks, h0, h50]
  change Eval (.call (StackRoutines.transferProgram 50 0 16 17))
    (3 * (b.stacks 50).length + 3) b ⟨out, StackRoutines.transferStacks 50 0 b.stacks⟩ at tf
  rw [hf] at tf
  have ti := initialize_eval p r Q Δ t.val g.val coefficients
    (TypeEnumeration.sideBytes r Q Δ t.val g.val) regs
  have hall := ti.seq (he'.seq tf)
  refine ⟨out, 2 + (n + (3 * (b.stacks 50).length + 3)) + 1, ?_,
    compiled_halt_trace hall 53 0⟩
  · have hb50 : (b.stacks 50).length = matrix.length := by simp [b, state]
    rw [hb50]
    dsimp [budget, matrix]
    omega

end SubexponentialSAT.Subexp.ConstraintMatrixProgram

end OAI.Algorithms
