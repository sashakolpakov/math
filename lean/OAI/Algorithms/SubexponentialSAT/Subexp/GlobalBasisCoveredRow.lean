import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisRowPrepare
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisRows

namespace OAI.Algorithms

/-! Actual preparation of one covered ambient row. The head color is read
from the type bytes, the Side list is physically generated, its row index is
computed, and the corresponding searched local table is loaded. -/

namespace SubexponentialSAT.Subexp.GlobalBasisCoveredRow

open BitProgram StructuredCalls
open MulticolorTypes

abbrev Data := GlobalBasisRowPrepare.Data
abbrev Code := GlobalBasisRowPrepare.Code
abbrev Store := Fin 64 → List Bool
abbrev unary (n : ℕ) := List.replicate n true

def context {r Q Δ : ℕ} (u : UniversalType r Q Δ) (t : Fin Q) : TypeFiberProgram.Context :=
  ⟨r, t.val, (u.head t).val, 0, 0⟩

def sideWords {r Q Δ : ℕ} (u : UniversalType r Q Δ) (t : Fin Q) :=
  TypeEnumeration.sideBytes r Q Δ t.val (u.head t).val

def coordinate {r Q Δ : ℕ} (u : UniversalType r Q Δ) (t : Fin Q) :=
  (sideWords u t).idxOf (CollisionProgram.encodeType u)

def workPorts : List (Fin 64) :=
  [0,1,2,4,8,9,10,11,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,41,42,43,44]

structure Input {r Q Δ : ℕ} (u : UniversalType r Q Δ) (t : Fin Q)
    (before : List (List Bool)) (N split : ℕ) (table tail : List Bool) (d : Data) : Prop where
  type : d.stacks 36 = CollisionProgram.encodeType u
  position : d.stacks 32 = unary t.val
  universal : d.stacks 37 = ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ)
  colors : d.stacks 38 = unary r
  batch : d.stacks 40 = GlobalBasisRecordLookup.recordsPrefix before ++
    GlobalBasisRecordLookup.record (SubexpLocalBatchParse.payload N split table) ++ tail
  colorIndex : before.length = (u.head t).val
  work : ∀ i ∈ workPorts, d.stacks i = []

def prepared {r Q Δ : ℕ} (s : Store) (u : UniversalType r Q Δ) (t : Fin Q)
    (N : ℕ) (table : List Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update s
    4 (unary (u.head t).val)) 2 (unary (coordinate u t))) 1 (unary N)) 0 table

def budget {r Q Δ : ℕ} (u : UniversalType r Q Δ) (t : Fin Q) (N split : ℕ)
    (batch : List Bool) : ℕ :=
  SubexpHeadColorProgram.budget t.val r + 1 +
    TypeFiberProgram.budget false (context u t) (TypeEnumeration.universalBytes r Q Δ) +
    SubexpNodeIndexProgram.Internal.budget (CollisionProgram.encodeType u) (sideWords u t) +
    60 * (batch.length + (u.head t).val + 1) +
    2 * (ProgramEncoding.encodeRecords (sideWords u t)).length + 2 * split + 2 * (N - split) + 9

theorem records_filter_length_le (keep : List Bool → Bool) (words : List (List Bool)) :
    (ProgramEncoding.encodeRecords (words.filter keep)).length ≤
      (ProgramEncoding.encodeRecords words).length := by
  induction words with
  | nil => exact le_rfl
  | cons bits words ih =>
      cases hk : keep bits <;>
        simp [hk, ProgramEncoding.encodeRecords,
          Encoding.length_encodeList_cons] at * <;> omega

theorem filter_budget_le (keep : Bool) (words : List (List Bool)) (index : ℕ) :
    TypeBitFilter.budget keep words index ≤
      (12 * index + 100) * ((ProgramEncoding.encodeRecords words).length + 1) := by
  have hb := RecordPrograms.program_budget_le_input
    (TypeBitFilter.callbackCost index) words 20 (12 * index + 40)
    (by intros; exact le_rfl)
  have hf := records_filter_length_le (TypeBitFilter.test keep index) words
  have hr : (ProgramEncoding.encodeRecords
      ((words.filter (TypeBitFilter.test keep index)).reverse)).length ≤
      (ProgramEncoding.encodeRecords words).length := by
    simpa only [ProgramEncoding.encodeRecords_length, List.map_reverse,
      List.sum_reverse, List.length_reverse] using hf
  unfold TypeBitFilter.budget
  nlinarith only [hb, hr, Nat.zero_le (ProgramEncoding.encodeRecords words).length]

/-- A common bound on the physically stored local parameters and streams
bounds the complete preparation. The untouched global streams and prior
matrix output do not enter this cost. -/
theorem budget_le {r Q Δ : ℕ} (u : UniversalType r Q Δ) (t : Fin Q)
    (N split : ℕ) (batch : List Bool) (W : ℕ)
    (hr : r ≤ W) (ht : t.val ≤ W)
    (hq : (CollisionProgram.encodeType u).length ≤ W)
    (hu : (ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ)).length ≤ W)
    (hb : batch.length ≤ W) (hN : N ≤ W) (hs : split ≤ W) :
    budget u t N split batch + 1 ≤ 500 * (W + 1)^3 := by
  let A := W + 1
  have hg : (u.head t).val ≤ W := (Nat.le_of_lt (u.head t).isLt).trans hr
  have htr : t.val * r ≤ W * W := Nat.mul_le_mul ht hr
  have hi : (context u t).offset false ≤ W * W + W := by
    dsimp [context, TypeFiberProgram.Context.offset, TypeEnumeration.headIndex]
    omega
  have hv : (ProgramEncoding.encodeRecords (sideWords u t)).length ≤ W :=
    (records_filter_length_le _ _).trans hu
  have hfilter : TypeBitFilter.budget true (TypeEnumeration.universalBytes r Q Δ)
      ((context u t).offset false) ≤ 100 * A^3 := by
    calc
      _ ≤ (12 * ((context u t).offset false) + 100) *
          ((ProgramEncoding.encodeRecords (TypeEnumeration.universalBytes r Q Δ)).length + 1) :=
        filter_budget_le _ _ _
      _ ≤ (12 * (W * W + W) + 100) * (W + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      _ ≤ (100 * (W + 1)^2) * (W + 1) :=
        Nat.mul_le_mul_right _ (by nlinarith only [Nat.zero_le W, Nat.zero_le (W * W)])
      _ = 100 * A^3 := by dsimp [A]; ring
  have hhead : SubexpHeadColorProgram.budget t.val r + 1 ≤ 40 * A^2 := by
    dsimp [SubexpHeadColorProgram.budget, A]
    nlinarith only [htr, ht, hr, Nat.zero_le W, Nat.zero_le (W * W)]
  have hprepare : TypeFiberProgram.prepareCost false (context u t) ≤ 25 * A^2 := by
    dsimp [TypeFiberProgram.prepareCost, TypeIndexProgram.headCost, context, A]
    nlinarith only [htr, hg, ht, Nat.zero_le W, Nat.zero_le (W * W)]
  have hindex : 2 * (context u t).offset false + 4 ≤ 5 * A^2 := by
    dsimp [A]
    nlinarith only [hi, Nat.zero_le W, Nat.zero_le (W * W)]
  have hfiber : TypeFiberProgram.budget false (context u t)
      (TypeEnumeration.universalBytes r Q Δ) ≤ 100 * A^3 + 30 * A^2 := by
    change TypeFiberProgram.prepareCost false (context u t) +
      TypeBitFilter.budget true (TypeEnumeration.universalBytes r Q Δ)
        ((context u t).offset false) + 2 * (context u t).offset false + 4 ≤ _
    omega
  have hnode : SubexpNodeIndexProgram.Internal.budget
      (CollisionProgram.encodeType u) (sideWords u t) ≤ 90 * A^2 := by
    unfold SubexpNodeIndexProgram.Internal.budget
    calc
      _ ≤ (9 * W + 80) * (W + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ 90 * A^2 := by
        dsimp [A]
        nlinarith only [Nat.zero_le W, Nat.zero_le (W * W)]
  have hlookup : 60 * (batch.length + (u.head t).val + 1) ≤ 120 * A := by
    dsimp [A]
    omega
  have hcleanup : 2 * (ProgramEncoding.encodeRecords (sideWords u t)).length +
      2 * split + 2 * (N - split) + 10 ≤ 10 * A := by
    dsimp [A]
    omega
  have hp12 : A ≤ A^2 := by
    calc
      A ≤ A + W * A := by omega
      _ = A^2 := by dsimp [A]; ring
  have hp23 : A^2 ≤ A^3 := by
    calc
      A^2 ≤ A^2 + W * A^2 := by omega
      _ = A^3 := by dsimp [A]; ring
  unfold budget
  change _ ≤ 500 * A^3
  omega

def cleared (src : Fin 64) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem clear_eval (src : Fin 64) (d : Data) :
    Eval (GlobalBasisRowPrepare.clear src) (2 * (d.stacks src).length + 3) d (cleared src d) :=
  .call _ (ListRegisterProgram.clear_run src (0 : Fin 16) 1 d.regs d.stacks)

theorem command_eval {r Q Δ : ℕ} (u : UniversalType r Q Δ) (t : Fin Q)
    (before : List (List Bool)) (N split : ℕ) (table tail : List Bool) (d : Data)
    (H : Input u t before N split table tail d) :
    ∃ n e, n ≤ budget u t N split (d.stacks 40) ∧
      Eval GlobalBasisRowPrepare.covered n d e ∧
      e.stacks = prepared d.stacks u t N table ∧ e.regs 6 = d.regs 6 := by
  have hhead : SubexpHeadColorProgram.Clean
      (projectState GlobalBasisRowPrepare.smallRegs GlobalBasisRowPrepare.headPorts d) := by
    intro i hi
    fin_cases i <;> simp at hi
    all_goals exact H.work _ (by decide)
  obtain ⟨n₁, a, hn₁, he₁, hs₁, hr₁⟩ := GlobalBasisRowPrepare.headColor_eval u t d
    H.type H.position H.colors hhead
  have hside : projectState GlobalBasisRowPrepare.workRegs GlobalBasisRowPrepare.sidePorts a =
      TypeFiberProgram.inputState (context u t) (TypeEnumeration.universalBytes r Q Δ)
        (a.regs ∘ GlobalBasisRowPrepare.workRegs) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [GlobalBasisRowPrepare.sidePorts, context, hs₁, H.universal, H.colors, H.position,
        TypeIndexProgram.unary, SubexpHeadColorProgram.unary, unary]
    all_goals exact H.work _ (by decide)
  obtain ⟨n₂, b, hn₂, he₂, hs₂, hr₂⟩ := GlobalBasisRowPrepare.side_eval
    (context u t) (TypeEnumeration.universalBytes r Q Δ) a hside
  have hresult : TypeFiberProgram.resultWords false (context u t)
      (TypeEnumeration.universalBytes r Q Δ) = sideWords u t := by
    change List.filter (TypeBitFilter.test true (TypeEnumeration.headIndex r t.val (u.head t).val))
      (TypeEnumeration.universalBytes r Q Δ) = _
    apply congrArg (fun p : List Bool → Bool => (TypeEnumeration.universalBytes r Q Δ).filter p)
    funext bits
    simp [TypeBitFilter.test]
  have hs₂' : b.stacks = Function.update a.stacks 41 (ProgramEncoding.encodeRecords (sideWords u t)) := by
    simpa only [hresult] using hs₂
  have hrank : projectState GlobalBasisRowPrepare.smallRegs GlobalBasisRowPrepare.rankPorts b =
      SubexpNodeIndexProgram.Internal.state (b.regs ∘ GlobalBasisRowPrepare.smallRegs)
        (CollisionProgram.encodeType u) (ProgramEncoding.encodeRecords (sideWords u t)) [] [] [] [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [GlobalBasisRowPrepare.rankPorts, SubexpNodeIndexProgram.Internal.store,
        hs₂', hs₁, H.type]
    all_goals exact H.work _ (by decide)
  obtain ⟨n₃, c, hn₃, he₃, hs₃, hr₃⟩ := GlobalBasisRowPrepare.rank_eval
    (CollisionProgram.encodeType u) (sideWords u t) b hrank
  have htable : GlobalBasisDataLookup.Clean
      (projectState GlobalBasisRowPrepare.workRegs GlobalBasisRowPrepare.tablePorts c) := by
    intro i hi hj
    fin_cases i <;> norm_num [Fin.coe_ofNat_eq_mod] at hi <;>
      norm_num [Fin.coe_ofNat_eq_mod] at hj
    all_goals
      simp [projectState, GlobalBasisRowPrepare.tablePorts, hs₃, hs₂', hs₁]
      exact H.work _ (by decide)
  obtain ⟨n₄, f, hn₄, he₄, hs₄, hr₄⟩ := GlobalBasisRowPrepare.localTable_eval before N split table tail c
    (by simpa [hs₃, hs₂', hs₁] using H.batch)
    (by simp [hs₃, hs₂', hs₁, H.colorIndex, GlobalBasisRecordLookup.unary]) htable
  let g := cleared 41 f
  let h := cleared 43 g
  let e := cleared 44 h
  have hc₁ : Eval (GlobalBasisRowPrepare.clear 41)
      (2 * (ProgramEncoding.encodeRecords (sideWords u t)).length + 3) f g := by
    simpa [hs₄, hs₃, hs₂'] using clear_eval 41 f
  have hc₂ : Eval (GlobalBasisRowPrepare.clear 43) (2 * split + 3) g h := by
    simpa [h, g, cleared, hs₄, GlobalBasisRecordLookup.unary] using clear_eval 43 g
  have hc₃ : Eval (GlobalBasisRowPrepare.clear 44) (2 * (N - split) + 3) h e := by
    simpa [e, h, g, cleared, hs₄, GlobalBasisRecordLookup.unary] using clear_eval 44 h
  refine ⟨n₁ + (n₂ + (n₃ + (n₄ + ((2 * (ProgramEncoding.encodeRecords (sideWords u t)).length + 3) +
      ((2 * split + 3) + (2 * (N - split) + 3)))))), e, ?_,
    he₁.seq (he₂.seq (he₃.seq (he₄.seq (hc₁.seq (hc₂.seq hc₃))))), ?_, ?_⟩
  · have hc40 : c.stacks 40 = d.stacks 40 := by simp [hs₃, hs₂', hs₁]
    have hc4 : (c.stacks 4).length = (u.head t).val := by
      simp [hs₃, hs₂', hs₁, SubexpHeadColorProgram.unary]
    rw [hc40, hc4] at hn₄
    unfold budget
    omega
  · funext i
    by_cases hi41 : i = 41 <;> by_cases hi43 : i = 43 <;> by_cases hi44 : i = 44 <;>
      simp [e, h, g, cleared, hs₄, hs₃, hs₂', hs₁, prepared, coordinate,
        GlobalBasisRecordLookup.unary, SubexpHeadColorProgram.unary, unary,
        Function.update_apply, hi41, hi43, hi44,
        H.work 41 (by decide), H.work 43 (by decide), H.work 44 (by decide)]
  · simpa [e, h, g, cleared, readRegs] using hr₄.trans (hr₃.trans (hr₂.trans hr₁))

theorem prepared_frame {r Q Δ : ℕ} (s : Store) (u : UniversalType r Q Δ) (t : Fin Q)
    (N : ℕ) (table : List Bool) (i : Fin 64)
    (h0 : i ≠ 0) (h1 : i ≠ 1) (h2 : i ≠ 2) (h4 : i ≠ 4) :
    prepared s u t N table i = s i := by simp [prepared, h0, h1, h2, h4]

theorem type_mem_side {r Q Δ : ℕ} (u : UniversalType r Q Δ) (t : Fin Q) :
    CollisionProgram.encodeType u ∈ sideWords u t := by
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le (u.head t).val) (u.head t).isLt
  have hQ : 0 < Q := lt_of_le_of_lt (Nat.zero_le t.val) t.isLt
  apply List.mem_filter.mpr
  refine ⟨TypeEnumeration.universalBytes_encode_mem hr hQ u, ?_⟩
  calc
    _ = decide (u.head t = u.head t) := TypeEnumeration.encodeType_head u t (u.head t)
    _ = true := by simp

theorem coordinate_lt {r Q Δ : ℕ} (u : UniversalType r Q Δ) (t : Fin Q) :
    coordinate u t < (sideWords u t).length := by
  simpa only [coordinate, List.idxOf, beq_eq_decide] using
    List.idxOf_lt_length_iff.mpr (type_mem_side u t)

def lowPorts : Fin 32 → Fin 64 := Fin.castAdd 32

def RowReady {p : ℕ} [Fact p.Prime] (R : GlobalBasisEntry.Row p) (d : Data) : Prop :=
  GlobalBasisRows.Invariant R (projectState id lowPorts d)

def row {p r Q Δ : ℕ} (u : UniversalType r Q Δ) (t : Fin Q) (block N : ℕ)
    (table : Fin N → Fin N → ZMod p) : GlobalBasisEntry.Row p :=
  ⟨N, table, coordinate u t, block, (u.head t).val, 0, true⟩

theorem prepared_ready {p r Q Δ : ℕ} [Fact p.Prime]
    (u : UniversalType r Q Δ) (t : Fin Q) (before : List (List Bool)) (N split block : ℕ)
    (table : Fin N → Fin N → ZMod p) (tail : List Bool) (d e : Data)
    (H : Input u t before N split (BasisTransposeProgram.rows (MatrixWordEncoding.code p) table).flatten tail d)
    (h3 : d.stacks 3 = unary block) (h5 : d.stacks 5 = [])
    (h13 : d.stacks 13 = unary (GlobalBasisEntry.frameWidth p))
    (h14 : d.stacks 14 = GlobalBasisEntry.scalarFrame p 0)
    (h15 : d.stacks 15 = GlobalBasisEntry.scalarFrame p 1)
    (hs : e.stacks = prepared d.stacks u t N (BasisTransposeProgram.rows (MatrixWordEncoding.code p) table).flatten)
    (hr : e.regs 6 = true) : RowReady (row u t block N table) e := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · simp [projectState, lowPorts, hs, prepared, row]
    · simp [projectState, lowPorts, hs, prepared, row, GlobalBasisEntryCore.unary, unary]
    · simp [projectState, lowPorts, hs, prepared, row, GlobalBasisEntryCore.unary, unary]
    · simpa [projectState, lowPorts, hs, prepared, row, GlobalBasisEntryCore.unary, unary] using h3
    · simp [projectState, lowPorts, hs, prepared, row, GlobalBasisEntryCore.unary, unary]
    · simp [projectState, lowPorts, hs, prepared, row, GlobalBasisEntryCore.unary, unary, h5]
    · simpa [projectState, lowPorts, hs, prepared, row, GlobalBasisEntryCore.unary, unary] using h13
    · simpa [projectState, lowPorts, hs, prepared] using h14
    · simpa [projectState, lowPorts, hs, prepared] using h15
    · exact hr
    · simpa [projectState, lowPorts, hs, prepared] using H.work 11 (by decide)
    · intro i hi
      have hj : ∀ j : Fin 64, j.val < 8 → lowPorts i ≠ j := by
        intro j hj he
        have hv := congrArg Fin.val he
        change i.val = j.val at hv
        omega
      change e.stacks (lowPorts i) = []
      rw [hs, prepared_frame _ _ _ _ _ _ (hj 0 (by decide)) (hj 1 (by decide))
        (hj 2 (by decide)) (hj 4 (by decide))]
      apply H.work
      fin_cases i <;> norm_num [Fin.coe_ofNat_eq_mod] at hi
      all_goals decide
  · simpa [projectState, lowPorts, hs, prepared] using H.work 8 (by decide)
  · simpa [projectState, lowPorts, hs, prepared] using H.work 9 (by decide)
  · simpa [projectState, lowPorts, hs, prepared] using H.work 10 (by decide)

theorem command_ready {p r Q Δ : ℕ} [Fact p.Prime]
    (u : UniversalType r Q Δ) (t : Fin Q) (before : List (List Bool)) (N split block : ℕ)
    (table : Fin N → Fin N → ZMod p) (tail : List Bool) (d : Data)
    (H : Input u t before N split (BasisTransposeProgram.rows (MatrixWordEncoding.code p) table).flatten tail d)
    (h3 : d.stacks 3 = unary block) (h5 : d.stacks 5 = [])
    (h13 : d.stacks 13 = unary (GlobalBasisEntry.frameWidth p))
    (h14 : d.stacks 14 = GlobalBasisEntry.scalarFrame p 0)
    (h15 : d.stacks 15 = GlobalBasisEntry.scalarFrame p 1) (h6 : d.regs 6 = true)
    (hN : N = (sideWords u t).length) :
    ∃ n e, n ≤ budget u t N split (d.stacks 40) ∧
      Eval GlobalBasisRowPrepare.covered n d e ∧
      e.stacks = prepared d.stacks u t N (BasisTransposeProgram.rows (MatrixWordEncoding.code p) table).flatten ∧
      RowReady (row u t block N table) e ∧ coordinate u t < N := by
  obtain ⟨n, e, hn, he, hs, hr⟩ := command_eval u t before N split _ tail d H
  exact ⟨n, e, hn, he, hs, prepared_ready u t before N split block table tail d e H
    h3 h5 h13 h14 h15 hs (hr.trans h6), by simpa only [hN] using coordinate_lt u t⟩

def program := compiled GlobalBasisRowPrepare.covered 36 0

theorem program_trace {n : ℕ} {d e : Data} (h : Eval GlobalBasisRowPrepare.covered n d e) :
    Trace program (n + 1) (d.withPC (some program.entry)) (e.withPC none) := compiled_halt_trace h 36 0

theorem program_primitive {n bound : ℕ} {d e : Data}
    (he : Eval GlobalBasisRowPrepare.covered n d e) (hn : n + 1 ≤ bound) :
    Computation.RunsIn (primitive program).step (primitiveOverhead program * bound)
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) := by
  obtain ⟨steps, hsteps, ht⟩ := primitive_trace program (program_trace he)
  exact ⟨steps, hsteps.trans (Nat.mul_le_mul_left _ hn), ht⟩

end SubexponentialSAT.Subexp.GlobalBasisCoveredRow

end OAI.Algorithms
