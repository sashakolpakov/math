import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisEntryCore
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisColumns

namespace OAI.Algorithms

/-! The actual global-matrix entry callback. Descriptor bytes are parsed and
compared at runtime. Matching local entries invoke the persistent scalar-cell
reader; the other branches copy the canonical zero or one frame. -/

namespace SubexponentialSAT.Subexp.GlobalBasisEntry

open BitProgram StructuredCalls SubexpScanPrimitives
open GlobalBasisEntryCore
open GlobalBasisColumns (Descriptor)

abbrev Data := GlobalBasisEntryCore.Data
abbrev Code := GlobalBasisEntryCore.Code
abbrev Store := GlobalBasisEntryCore.Store

structure Row (p : ℕ) where
  N : ℕ
  table : Fin N → Fin N → ZMod p
  coordinate : ℕ
  block : ℕ
  color : ℕ
  rank : ℕ
  covered : Bool

def frameWidth (p : ℕ) : ℕ := 2 * MatrixWordEncoding.width p + 1
def scalarFrame (p : ℕ) (value : ZMod p) : List Bool :=
  Encoding.frame (MatrixWordEncoding.word p value)

@[simp] theorem scalarFrame_length (p : ℕ) (value : ZMod p) :
    (scalarFrame p value).length = frameWidth p := by
  simp [scalarFrame, frameWidth]

def Row.cell {p : ℕ} (R : Row p) (column : ℕ) : ZMod p :=
  if hr : R.coordinate < R.N then
    if hc : column < R.N then R.table ⟨R.coordinate, hr⟩ ⟨column, hc⟩ else 0
  else 0

def colorValue {p : ℕ} (R : Row p) (color column : ℕ) : ZMod p :=
  if R.color = color then R.cell column else 0

def blockValue {p : ℕ} (R : Row p) (block color column : ℕ) : ZMod p :=
  if R.block = block then colorValue R color column else 0

def localValue {p : ℕ} (R : Row p) (block color column : ℕ) : ZMod p :=
  if R.covered = true then blockValue R block color column else 0

def leftoverValue {p : ℕ} (R : Row p) (rank : ℕ) : ZMod p :=
  if R.covered = true then 0 else if R.rank = rank then 1 else 0

def value {p : ℕ} (R : Row p) : Descriptor → ZMod p
  | .localColumn block color column => localValue R block color column
  | .leftover rank => leftoverValue R rank

def Valid {p : ℕ} (R : Row p) : Descriptor → Prop
  | .localColumn block color column =>
      R.covered = true → R.block = block → R.color = color →
        R.coordinate < R.N ∧ column < R.N
  | .leftover _ => True

structure Ready {p : ℕ} [Fact p.Prime] (R : Row p) (d : Data) : Prop where
  table : d.stacks 0 = (BasisTransposeProgram.rows (MatrixWordEncoding.code p) R.table).flatten
  dimension : d.stacks 1 = unary R.N
  coordinate : d.stacks 2 = unary R.coordinate
  block : d.stacks 3 = unary R.block
  color : d.stacks 4 = unary R.color
  rank : d.stacks 5 = unary R.rank
  width : d.stacks 13 = unary (frameWidth p)
  zero : d.stacks 14 = scalarFrame p 0
  one : d.stacks 15 = scalarFrame p 1
  kind : d.regs 6 = R.covered
  output : d.stacks 11 = []
  work : ∀ i : Fin 32, 16 ≤ i.val → d.stacks i = []

theorem Ready.congr {p : ℕ} [Fact p.Prime] {R : Row p} {d e : Data} (H : Ready R d)
    (hs : e.stacks = d.stacks) (hr : e.regs 6 = d.regs 6) : Ready R e := by
  constructor
  all_goals first | simpa only [hs] using H.table | simpa only [hs] using H.dimension |
    simpa only [hs] using H.coordinate | simpa only [hs] using H.block |
    simpa only [hs] using H.color | simpa only [hs] using H.rank |
    simpa only [hs] using H.width | simpa only [hs] using H.zero |
    simpa only [hs] using H.one | exact hr.trans H.kind |
    simpa only [hs] using H.output | simpa only [hs] using H.work

theorem zero_eval {p : ℕ} [Fact p.Prime] {R : Row p} {d : Data} (H : Ready R d) :
    ∃ e, Eval (known 14) (7 * frameWidth p + 5) d e ∧
      e.stacks = Function.update d.stacks 11 (scalarFrame p 0) ∧ e.regs 6 = d.regs 6 := by
  obtain ⟨e, he, hs, hr⟩ := known_eval 14 (by decide) (by decide) d H.output (H.work 31 (by decide))
  exact ⟨e, by simpa only [H.zero, scalarFrame_length] using he, by simpa only [H.zero] using hs, hr⟩

theorem one_eval {p : ℕ} [Fact p.Prime] {R : Row p} {d : Data} (H : Ready R d) :
    ∃ e, Eval (known 15) (7 * frameWidth p + 5) d e ∧
      e.stacks = Function.update d.stacks 11 (scalarFrame p 1) ∧ e.regs 6 = d.regs 6 := by
  obtain ⟨e, he, hs, hr⟩ := known_eval 15 (by decide) (by decide) d H.output (H.work 31 (by decide))
  exact ⟨e, by simpa only [H.one, scalarFrame_length] using he, by simpa only [H.one] using hs, hr⟩

def cellCost {p : ℕ} (R : Row p) (column : ℕ) : ℕ :=
  SubexpScalarCellRead.cost R.N R.coordinate column (frameWidth p)

theorem cell_eval {p : ℕ} [Fact p.Prime] {R : Row p} {d : Data} (H : Ready R d)
    (column : ℕ) (hc : d.stacks 10 = unary column)
    (hrange : R.coordinate < R.N ∧ column < R.N) :
    ∃ n e, n ≤ cellCost R column + 1 ∧ Eval cellCall n d e ∧
      e.stacks = Function.update d.stacks 11 (scalarFrame p (R.cell column)) ∧
      e.regs 6 = d.regs 6 := by
  obtain ⟨n, e, hn, he, hs, hr⟩ := cellCall_eval p R.N R.table
    ⟨R.coordinate, hrange.1⟩ ⟨column, hrange.2⟩ d H.table H.dimension H.coordinate hc H.width H.output
    (fun i hi _ => H.work i hi)
  exact ⟨n, e, hn, he, by simpa only [Row.cell, dite_eq_left hrange.1, dite_eq_left hrange.2, scalarFrame] using hs, hr⟩

def selectColor : Code := .seq (compare 4 9) (.ite 7 cellCall (known 14))
def selectBlock : Code := .seq (compare 3 8) (.ite 7 selectColor (known 14))
def selectLocal : Code := .ite 6 selectBlock (known 14)
def selectRank : Code := .seq (compare 5 8) (.ite 7 (known 15) (known 14))
def selectLeftover : Code := .ite 6 (known 14) selectRank

def colorCost {p : ℕ} (R : Row p) (color column : ℕ) : ℕ :=
  cellCost R column + 18 * R.color + 9 * color + 7 * frameWidth p + 37
def blockCost {p : ℕ} (R : Row p) (block color column : ℕ) : ℕ :=
  cellCost R column + 18 * (R.block + R.color) + 9 * (block + color) + 7 * frameWidth p + 69
def localCost {p : ℕ} (R : Row p) (block color column : ℕ) : ℕ :=
  blockCost R block color column + 1
def rankCost {p : ℕ} (R : Row p) (rank : ℕ) : ℕ :=
  18 * R.rank + 9 * rank + 7 * frameWidth p + 37
def leftoverCost {p : ℕ} (R : Row p) (rank : ℕ) : ℕ := rankCost R rank + 1

theorem selectColor_eval {p : ℕ} [Fact p.Prime] {R : Row p} {d : Data} (H : Ready R d)
    (color column : ℕ) (hg : d.stacks 9 = unary color) (hc : d.stacks 10 = unary column)
    (hvalid : R.color = color → R.coordinate < R.N ∧ column < R.N) :
    ∃ n e, n ≤ colorCost R color column ∧ Eval selectColor n d e ∧
      e.stacks = Function.update d.stacks 11 (scalarFrame p (colorValue R color column)) ∧
      e.regs 6 = d.regs 6 := by
  obtain ⟨n, a, hn, he, hs, hr, htest⟩ := compare_eval 4 9 (by decide) (by decide) d
    (H.work 17 (by decide)) (H.work 28 (by decide)) (H.work 27 (by decide)) (H.work 31 (by decide))
  have HA : Ready R a := H.congr hs hr
  have hna : n ≤ 18 * R.color + 9 * color + 31 := by simpa [H.color, hg] using hn
  have hta : a.regs 7 = decide (R.color = color) := by simpa [H.color, hg] using htest
  by_cases hmatch : R.color = color
  · obtain ⟨m, e, hm, hem, hse, hre⟩ := cell_eval HA column (by simpa [hs] using hc) (hvalid hmatch)
    refine ⟨n + (m + 1), e, ?_, he.seq (.ite_true (by simpa [hmatch] using hta) hem), ?_, hre.trans hr⟩
    · unfold colorCost; omega
    · simpa [hs, colorValue, hmatch] using hse
  · obtain ⟨e, hem, hse, hre⟩ := zero_eval HA
    refine ⟨n + (7 * frameWidth p + 5 + 1), e, ?_,
      he.seq (.ite_false (by simpa [hmatch] using hta) hem), ?_, hre.trans hr⟩
    · unfold colorCost; omega
    · simpa [hs, colorValue, hmatch] using hse

theorem selectBlock_eval {p : ℕ} [Fact p.Prime] {R : Row p} {d : Data} (H : Ready R d)
    (block color column : ℕ) (hb : d.stacks 8 = unary block)
    (hg : d.stacks 9 = unary color) (hc : d.stacks 10 = unary column)
    (hvalid : R.block = block → R.color = color → R.coordinate < R.N ∧ column < R.N) :
    ∃ n e, n ≤ blockCost R block color column ∧ Eval selectBlock n d e ∧
      e.stacks = Function.update d.stacks 11 (scalarFrame p (blockValue R block color column)) ∧
      e.regs 6 = d.regs 6 := by
  obtain ⟨n, a, hn, he, hs, hr, htest⟩ := compare_eval 3 8 (by decide) (by decide) d
    (H.work 17 (by decide)) (H.work 28 (by decide)) (H.work 27 (by decide)) (H.work 31 (by decide))
  have HA : Ready R a := H.congr hs hr
  have hna : n ≤ 18 * R.block + 9 * block + 31 := by simpa [H.block, hb] using hn
  have hta : a.regs 7 = decide (R.block = block) := by simpa [H.block, hb] using htest
  by_cases hmatch : R.block = block
  · obtain ⟨m, e, hm, hem, hse, hre⟩ := selectColor_eval HA color column
      (by simpa [hs] using hg) (by simpa [hs] using hc) (hvalid hmatch)
    refine ⟨n + (m + 1), e, ?_, he.seq (.ite_true (by simpa [hmatch] using hta) hem), ?_, hre.trans hr⟩
    · unfold blockCost colorCost at *; omega
    · simpa [hs, blockValue, hmatch] using hse
  · obtain ⟨e, hem, hse, hre⟩ := zero_eval HA
    refine ⟨n + (7 * frameWidth p + 5 + 1), e, ?_,
      he.seq (.ite_false (by simpa [hmatch] using hta) hem), ?_, hre.trans hr⟩
    · unfold blockCost; omega
    · simpa [hs, blockValue, hmatch] using hse

theorem selectLocal_eval {p : ℕ} [Fact p.Prime] {R : Row p} {d : Data} (H : Ready R d)
    (block color column : ℕ) (hb : d.stacks 8 = unary block)
    (hg : d.stacks 9 = unary color) (hc : d.stacks 10 = unary column)
    (hvalid : Valid R (.localColumn block color column)) :
    ∃ n e, n ≤ localCost R block color column ∧ Eval selectLocal n d e ∧
      e.stacks = Function.update d.stacks 11 (scalarFrame p (localValue R block color column)) ∧
      e.regs 6 = d.regs 6 := by
  by_cases hcovered : R.covered = true
  · obtain ⟨n, e, hn, he, hs, hr⟩ := selectBlock_eval H block color column hb hg hc (hvalid hcovered)
    exact ⟨n + 1, e, Nat.add_le_add_right hn 1, .ite_true (H.kind.trans hcovered) he,
      by simpa [localValue, hcovered] using hs, hr⟩
  · obtain ⟨e, he, hs, hr⟩ := zero_eval H
    refine ⟨7 * frameWidth p + 5 + 1, e, ?_, .ite_false ?_ he,
      by simpa [localValue, hcovered] using hs, hr⟩
    · unfold localCost blockCost; omega
    · rw [H.kind]; cases h : R.covered <;> simp_all

theorem selectRank_eval {p : ℕ} [Fact p.Prime] {R : Row p} {d : Data} (H : Ready R d)
    (rank : ℕ) (hx : d.stacks 8 = unary rank) :
    ∃ n e, n ≤ rankCost R rank ∧ Eval selectRank n d e ∧
      e.stacks = Function.update d.stacks 11 (scalarFrame p (if R.rank = rank then 1 else 0)) ∧
      e.regs 6 = d.regs 6 := by
  obtain ⟨n, a, hn, he, hs, hr, htest⟩ := compare_eval 5 8 (by decide) (by decide) d
    (H.work 17 (by decide)) (H.work 28 (by decide)) (H.work 27 (by decide)) (H.work 31 (by decide))
  have HA : Ready R a := H.congr hs hr
  have hna : n ≤ 18 * R.rank + 9 * rank + 31 := by simpa [H.rank, hx] using hn
  have hta : a.regs 7 = decide (R.rank = rank) := by simpa [H.rank, hx] using htest
  by_cases hmatch : R.rank = rank
  · obtain ⟨e, hem, hse, hre⟩ := one_eval HA
    refine ⟨n + (7 * frameWidth p + 5 + 1), e, ?_,
      he.seq (.ite_true (by simpa [hmatch] using hta) hem), ?_, hre.trans hr⟩
    · unfold rankCost; omega
    · simpa [hs, hmatch] using hse
  · obtain ⟨e, hem, hse, hre⟩ := zero_eval HA
    refine ⟨n + (7 * frameWidth p + 5 + 1), e, ?_,
      he.seq (.ite_false (by simpa [hmatch] using hta) hem), ?_, hre.trans hr⟩
    · unfold rankCost; omega
    · simpa [hs, hmatch] using hse

theorem selectLeftover_eval {p : ℕ} [Fact p.Prime] {R : Row p} {d : Data} (H : Ready R d)
    (rank : ℕ) (hx : d.stacks 8 = unary rank) :
    ∃ n e, n ≤ leftoverCost R rank ∧ Eval selectLeftover n d e ∧
      e.stacks = Function.update d.stacks 11 (scalarFrame p (leftoverValue R rank)) ∧
      e.regs 6 = d.regs 6 := by
  by_cases hcovered : R.covered = true
  · obtain ⟨e, he, hs, hr⟩ := zero_eval H
    refine ⟨7 * frameWidth p + 5 + 1, e, ?_, .ite_true (H.kind.trans hcovered) he,
      by simpa [leftoverValue, hcovered] using hs, hr⟩
    unfold leftoverCost rankCost; omega
  · obtain ⟨n, e, hn, he, hs, hr⟩ := selectRank_eval H rank hx
    refine ⟨n + 1, e, Nat.add_le_add_right hn 1, .ite_false ?_ he,
      by simpa [leftoverValue, hcovered] using hs, hr⟩
    rw [H.kind]; cases h : R.covered <;> simp_all

def firstIndex : Descriptor → ℕ
  | .localColumn block _ _ => block
  | .leftover rank => rank
def secondIndex : Descriptor → ℕ
  | .localColumn _ color _ => color
  | .leftover _ => 0
def thirdIndex : Descriptor → ℕ
  | .localColumn _ _ column => column
  | .leftover _ => 0
def localTag : Descriptor → Bool
  | .localColumn .. => true
  | .leftover _ => false
def descriptorSize (x : Descriptor) := firstIndex x + secondIndex x + thirdIndex x

def readLocal : Code := .seq (readField 8 (by decide))
  (.seq (readField 9 (by decide)) (readField 10 (by decide)))
def parse : Code := .seq (transfer 7 16)
  (.seq (pop 16) (.ite 7 readLocal (readField 8 (by decide))))

def parsed (s : Store) (x : Descriptor) : Store :=
  Function.update (Function.update (Function.update (Function.update s 7 [])
    8 (unary (firstIndex x))) 9 (unary (secondIndex x))) 10 (unary (thirdIndex x))

theorem parse_eval (x : Descriptor) (d : Data)
    (hp : d.stacks 7 = x.encode.reverse)
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) (h10 : d.stacks 10 = [])
    (h16 : d.stacks 16 = []) :
    ∃ n e, n ≤ 12 * descriptorSize x + 30 ∧ Eval parse n d e ∧
      e.stacks = parsed d.stacks x ∧ e.regs 6 = d.regs 6 ∧ e.regs 7 = localTag x := by
  let a := afterTransfer d 7 16 0 1
  have ha := SubexpScanPrimitives.transfer_eval d 7 16 0 1 (by decide) (by decide)
  have has : a.stacks 16 = x.encode := by
    simp [a, afterTransfer, StackRoutines.transferStacks, hp, h16]
  cases x with
  | localColumn block color column =>
    let body := Encoding.frame (unary block) ++ (Encoding.frame (unary color) ++ Encoding.frame (unary column))
    let b := popped 16 true body a
    have hpop := pop_eval 16 a true body (by
      simpa [Descriptor.encode, GlobalBasisColumns.localPayload, GlobalBasisColumns.unary,
        unary, body, List.append_assoc] using has)
    obtain ⟨c, hc, hcs, hc6, hc7⟩ := readField_eval 8 (by decide) b block
      (Encoding.frame (unary color) ++ Encoding.frame (unary column))
      (by simp [b, popped, body])
      (by simp [b, popped, a, afterTransfer, StackRoutines.transferStacks, h8])
    obtain ⟨f, hf, hfs, hf6, hf7⟩ := readField_eval 9 (by decide) c color
      (Encoding.frame (unary column)) (by simp [hcs])
      (by simp [hcs, b, popped, a, afterTransfer, StackRoutines.transferStacks, h9])
    obtain ⟨e, he, hes, he6, he7⟩ := readField_eval 10 (by decide) f column []
      (by simp [hfs])
      (by simp [hfs, hcs, b, popped, a, afterTransfer, StackRoutines.transferStacks, h10])
    refine ⟨(3 * (d.stacks 7).length + 3) +
      (1 + (((6 * block + 4) + ((6 * color + 4) + (6 * column + 4))) + 1)), e,
      ?_, ha.seq (hpop.seq (.ite_true (by simp [ popped, readRegs]) (hc.seq (hf.seq he)))),
      ?_, ?_, ?_⟩
    · simp [hp, Descriptor.encode, GlobalBasisColumns.localPayload, GlobalBasisColumns.unary,
        descriptorSize, firstIndex, secondIndex, thirdIndex]
      omega
    · funext j
      fin_cases j <;> simp [hes, hfs, hcs, b, popped, a, afterTransfer,
        StackRoutines.transferStacks, parsed, firstIndex, secondIndex, thirdIndex, h16]
    · rw [he6, hf6, hc6]
      simp [b, popped, a, afterTransfer, readRegs]
    · rw [he7, hf7, hc7]
      simp [b, popped, localTag, readRegs]
  | leftover rank =>
    let body := Encoding.frame (unary rank)
    let b := popped 16 false body a
    have hpop := pop_eval 16 a false body (by
      simpa [Descriptor.encode, GlobalBasisColumns.unary, unary, body] using has)
    obtain ⟨e, he, hes, he6, he7⟩ := readField_eval 8 (by decide) b rank []
      (by simp [b, popped, body])
      (by simp [b, popped, a, afterTransfer, StackRoutines.transferStacks, h8])
    refine ⟨(3 * (d.stacks 7).length + 3) + (1 + ((6 * rank + 4) + 1)), e,
      ?_, ha.seq (hpop.seq (.ite_false (by simp [ popped, readRegs]) he)), ?_, ?_, ?_⟩
    · simp [hp, Descriptor.encode, GlobalBasisColumns.unary,
        descriptorSize, firstIndex, secondIndex, thirdIndex]
      omega
    · funext j
      fin_cases j <;> simp [hes, b, popped, a, afterTransfer, StackRoutines.transferStacks,
        parsed, firstIndex, secondIndex, thirdIndex, unary, h9, h10, h16]
    · rw [he6]
      simp [b, popped, a, afterTransfer, readRegs]
    · rw [he7]
      simp [b, popped, localTag, readRegs]

theorem Ready.parsed {p : ℕ} [Fact p.Prime] {R : Row p} {d e : Data} (H : Ready R d)
    (x : Descriptor) (hs : e.stacks = parsed d.stacks x) (hr : e.regs 6 = d.regs 6) : Ready R e := by
  have keep (i : Fin 32) (h7 : i ≠ 7) (h8 : i ≠ 8) (h9 : i ≠ 9)
      (h10 : i ≠ 10) : GlobalBasisEntry.parsed d.stacks x i = d.stacks i := by
    simp only [GlobalBasisEntry.parsed, Function.update_of_ne h10, Function.update_of_ne h9,
      Function.update_of_ne h8, Function.update_of_ne h7]
  constructor
  · rw [hs, keep 0 (by decide) (by decide) (by decide) (by decide)]; exact H.table
  · rw [hs, keep 1 (by decide) (by decide) (by decide) (by decide)]; exact H.dimension
  · rw [hs, keep 2 (by decide) (by decide) (by decide) (by decide)]; exact H.coordinate
  · rw [hs, keep 3 (by decide) (by decide) (by decide) (by decide)]; exact H.block
  · rw [hs, keep 4 (by decide) (by decide) (by decide) (by decide)]; exact H.color
  · rw [hs, keep 5 (by decide) (by decide) (by decide) (by decide)]; exact H.rank
  · rw [hs, keep 13 (by decide) (by decide) (by decide) (by decide)]; exact H.width
  · rw [hs, keep 14 (by decide) (by decide) (by decide) (by decide)]; exact H.zero
  · rw [hs, keep 15 (by decide) (by decide) (by decide) (by decide)]; exact H.one
  · exact hr.trans H.kind
  · rw [hs, keep 11 (by decide) (by decide) (by decide) (by decide)]; exact H.output
  · intro i hi
    have h7 : i ≠ 7 := (low_ne_high 7 i (by decide) hi).symm
    have h8 : i ≠ 8 := (low_ne_high 8 i (by decide) hi).symm
    have h9 : i ≠ 9 := (low_ne_high 9 i (by decide) hi).symm
    have h10 : i ≠ 10 := (low_ne_high 10 i (by decide) hi).symm
    rw [hs]
    simpa only [SubexponentialSAT.Subexp.GlobalBasisEntry.parsed, Function.update_of_ne h10,
      Function.update_of_ne h9, Function.update_of_ne h8, Function.update_of_ne h7] using H.work i hi

def selection : Code := .ite 7 selectLocal selectLeftover
def selectionCost {p : ℕ} (R : Row p) : Descriptor → ℕ
  | .localColumn block color column => localCost R block color column + 1
  | .leftover rank => leftoverCost R rank + 1

theorem selection_eval {p : ℕ} [Fact p.Prime] {R : Row p} {d : Data} (H : Ready R d)
    (x : Descriptor) (h8 : d.stacks 8 = unary (firstIndex x))
    (h9 : d.stacks 9 = unary (secondIndex x)) (h10 : d.stacks 10 = unary (thirdIndex x))
    (htag : d.regs 7 = localTag x) (hvalid : Valid R x) :
    ∃ n e, n ≤ selectionCost R x ∧ Eval selection n d e ∧
      e.stacks = Function.update d.stacks 11 (scalarFrame p (value R x)) ∧ e.regs 6 = d.regs 6 := by
  cases x with
  | localColumn block color column =>
    obtain ⟨n, e, hn, he, hs, hr⟩ := selectLocal_eval H block color column h8 h9 h10 hvalid
    exact ⟨n + 1, e, Nat.add_le_add_right hn 1, .ite_true htag he, hs, hr⟩
  | leftover rank =>
    obtain ⟨n, e, hn, he, hs, hr⟩ := selectLeftover_eval H rank h8
    exact ⟨n + 1, e, Nat.add_le_add_right hn 1, .ite_false htag he, hs, hr⟩

def command : Code := .seq parse (.seq selection finish)
def program := compiled command 7 12
def entryFrame {p : ℕ} (R : Row p) (x : Descriptor) : List Bool := scalarFrame p (value R x)
def output (s : Store) (frame : List Bool) : Store :=
  Function.update (Function.update s 7 []) 12 (frame.reverse ++ s 12)

def cost {p : ℕ} (R : Row p) (x : Descriptor) : ℕ :=
  cellCost R (thirdIndex x) +
    100 * (R.block + R.color + R.rank + descriptorSize x + frameWidth p + 2)

theorem cost_assembly {p : ℕ} (R : Row p) (x : Descriptor) :
    12 * descriptorSize x + 30 + (selectionCost R x +
      (3 * frameWidth p + 2 * descriptorSize x + 15)) ≤ cost R x := by
  cases x <;> simp only [cost, selectionCost, localCost, blockCost, leftoverCost, rankCost,
    descriptorSize, firstIndex, secondIndex, thirdIndex] <;> omega

/-- The input table, canonical zero/one frames, and descriptor are actual
stored bytes. Bounds are needed only when the local descriptor matches. -/
theorem command_eval {p : ℕ} [Fact p.Prime] {R : Row p} {d : Data} (H : Ready R d)
    (x : Descriptor) (hp : d.stacks 7 = x.encode.reverse)
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) (h10 : d.stacks 10 = [])
    (hvalid : Valid R x) :
    ∃ n e, n ≤ cost R x ∧ Eval command n d e ∧ e.stacks = output d.stacks (entryFrame R x) ∧
      e.regs 6 = d.regs 6 ∧ e.regs 13 = false ∧ e.regs 14 = true ∧ e.regs 15 = false := by
  obtain ⟨n, a, hn, ha, has, ha6, ha7⟩ := parse_eval x d hp h8 h9 h10 (H.work 16 (by decide))
  obtain ⟨m, b, hm, hb, hbs, hb6⟩ := selection_eval (H.parsed x has ha6) x
    (by simp [has, parsed]) (by simp [has, parsed]) (by simp [has, parsed]) ha7 hvalid
  obtain ⟨e, he, hes, he6, he13, he14, he15⟩ := finish_eval b
  have hb11 : b.stacks 11 = entryFrame R x := by simp [hbs, entryFrame]
  have hb8 : b.stacks 8 = unary (firstIndex x) := by simp [hbs, has, parsed]
  have hb9 : b.stacks 9 = unary (secondIndex x) := by simp [hbs, has, parsed]
  have hb10 : b.stacks 10 = unary (thirdIndex x) := by simp [hbs, has, parsed]
  rw [hb11, hb8, hb9, hb10] at he
  simp only [entryFrame, scalarFrame_length, unary_length] at he
  refine ⟨n + (m + (3 * frameWidth p + 2 * descriptorSize x + 15)), e, ?_,
    ha.seq (hb.seq he), ?_, he6.trans (hb6.trans ha6), he13, he14, he15⟩
  · exact (Nat.add_le_add hn (Nat.add_le_add_right hm _)).trans (cost_assembly R x)
  · funext j
    fin_cases j <;> simp [hes, finished, hbs, has, parsed, output, entryFrame,
      h8, h9, h10, H.output]

def localSize {p : ℕ} (R : Row p) (x : Descriptor) : ℕ :=
  R.N + R.coordinate + R.block + R.color + R.rank + frameWidth p + descriptorSize x + 1

theorem cost_le_cubic {p : ℕ} (R : Row p) (x : Descriptor) :
    cost R x + 1 ≤ 1000 * (localSize R x)^3 := by
  let L := localSize R x
  have hL : 1 ≤ L := by dsimp [L, localSize]; omega
  have hcol : thirdIndex x ≤ descriptorSize x := by unfold descriptorSize; omega
  have hbase : R.N + R.coordinate + thirdIndex x + frameWidth p + 1 ≤ L := by
    dsimp [L, localSize]; omega
  have hc := (SubexpScalarCellRead.cost_le_cubic R.N R.coordinate (thirdIndex x) (frameWidth p)).trans
    (Nat.mul_le_mul_left 120 (Nat.pow_le_pow_left hbase 3))
  have hL2 : L ≤ L * L := by nlinarith
  have hL3 : L * L ≤ L * L * L := Nat.mul_le_mul_right L hL2
  have hlinear : R.block + R.color + R.rank + descriptorSize x + frameWidth p + 2 ≤ 2 * L := by
    dsimp [L, localSize]; omega
  change cost R x + 1 ≤ 1000 * L^3
  unfold cost cellCost
  nlinarith

def localInputSize (d : Data) : ℕ :=
  (d.stacks 1).length + (d.stacks 2).length + (d.stacks 3).length + (d.stacks 4).length +
    (d.stacks 5).length + (d.stacks 13).length + (d.stacks 7).length + 1

theorem localSize_le_input {p : ℕ} [Fact p.Prime] {R : Row p} {d : Data} (H : Ready R d)
    (x : Descriptor) (hp : d.stacks 7 = x.encode.reverse) : localSize R x ≤ localInputSize d := by
  have hx : descriptorSize x ≤ x.encode.length := by
    cases x <;> simp [descriptorSize, firstIndex, secondIndex, thirdIndex,
      Descriptor.encode, GlobalBasisColumns.localPayload, GlobalBasisColumns.unary] <;> omega
  simp only [localSize, localInputSize, H.dimension, H.coordinate, H.block, H.color, H.rank,
    H.width, hp, unary_length, List.length_reverse]
  omega

theorem command_serialized {p : ℕ} [Fact p.Prime] {R : Row p} {d : Data} (H : Ready R d)
    (x : Descriptor) (hp : d.stacks 7 = x.encode.reverse)
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) (h10 : d.stacks 10 = [])
    (hvalid : Valid R x) :
    ∃ n e, n + 1 ≤ 1000 * (localInputSize d)^3 ∧ Eval command n d e ∧
      e.stacks = output d.stacks (entryFrame R x) ∧
      e.regs 6 = d.regs 6 ∧ e.regs 13 = false ∧ e.regs 14 = true ∧ e.regs 15 = false := by
  obtain ⟨n, e, hn, he, hs, hr⟩ := command_eval H x hp h8 h9 h10 hvalid
  exact ⟨n, e, (Nat.add_le_add_right hn 1).trans ((cost_le_cubic R x).trans
    (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left (localSize_le_input H x hp) 3))), he, hs, hr⟩

theorem program_trace {n : ℕ} {d e : Data} (h : Eval command n d e) :
    Trace program (n + 1) (d.withPC (some program.entry)) (e.withPC none) := compiled_halt_trace h 7 12

theorem program_primitive {n bound : ℕ} {d e : Data} (he : Eval command n d e) (hn : n + 1 ≤ bound) :
    Computation.RunsIn (primitive program).step (primitiveOverhead program * bound)
      (primitiveCfg program (d.withPC (some program.entry)))
      (primitiveCfg program (e.withPC none)) := by
  obtain ⟨steps, hsteps, ht⟩ := primitive_trace program (program_trace he)
  exact ⟨steps, hsteps.trans (Nat.mul_le_mul_left _ hn), ht⟩

end SubexponentialSAT.Subexp.GlobalBasisEntry

end OAI.Algorithms
