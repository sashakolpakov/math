import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTripleProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramFold
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanContractLoop

namespace OAI.Algorithms

/-! The input/output of the dynamic expander is exactly the k-major table and
triple stream used by the native ring contraction. `List.ofFn` below describes
the serialized input and theorem; the fixed program builds the repeated stream
by actual counted loops and paid source copies. -/
namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpQuarticRing

def coordinateRows {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) (k : Fin d) : List (Row B) :=
  List.ofFn fun i : Fin d => (x i, List.ofFn fun j : Fin d => (y j, table i j k))

def matrices {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) : List (List (Row B)) :=
  List.ofFn fun k : Fin d => coordinateRows table x y k

def tableEncoding {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B) : List Bool :=
  (List.ofFn fun k : Fin d => (List.ofFn fun i : Fin d =>
    (List.ofFn fun j : Fin d => (table i j k).val).flatten).flatten).flatten

def blocks {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) : List (List (RingScan.WordTriple B)) :=
  List.ofFn fun k : Fin d => RingProgram.coordinateTriples table x y k

def layout (x y degree width : List Bool) : Store where
  x := x
  y := y
  table := []
  out := []
  xs := []
  ys := []
  held := []
  degree := degree
  kc := []
  ic := []
  jc := []
  width := width

theorem xBits_map {B : ℕ} (rows : List (Row B)) :
    xBits rows = (rows.map fun r => r.1.val).flatten := by
  induction rows with
  | nil => rfl
  | cons r rows ih => simp only [xBits, List.map_cons, List.flatten_cons, ih]

theorem leftBits_map {B : ℕ} (pairs : List (Word B × Word B)) :
    leftBits pairs = (pairs.map fun p => p.1.val).flatten := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih => simp only [leftBits, List.map_cons, List.flatten_cons, ih]

theorem rightBits_map {B : ℕ} (pairs : List (Word B × Word B)) :
    rightBits pairs = (pairs.map fun p => p.2.val).flatten := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih => simp only [rightBits, List.map_cons, List.flatten_cons, ih]

theorem tableBits_map {B : ℕ} (rows : List (Row B)) :
    tableBits rows = (rows.map fun r => rightBits r.2).flatten := by
  induction rows with
  | nil => rfl
  | cons r rows ih => simp only [tableBits, List.map_cons, List.flatten_cons, ih]

theorem allTableBits_map {B : ℕ} (ms : List (List (Row B))) :
    allTableBits ms = (ms.map tableBits).flatten := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp only [allTableBits, List.map_cons, List.flatten_cons, ih]

theorem table_encoding {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) :
    allTableBits (matrices table x y) = tableEncoding table := by
  simp [allTableBits_map, matrices, coordinateRows, tableBits_map,
    rightBits_map, List.map_ofFn, tableEncoding, Function.comp_def]

theorem matrices_fit {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) (degree width : List Bool)
    (hd : degree.length = d) :
    ∀ m ∈ matrices table x y,
      MatrixFits (layout (RingProgram.flat x) (RingProgram.flat y) degree width) m := by
  intro m hm
  obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hm
  refine ⟨?_, ?_, ?_⟩
  · simp [coordinateRows, xBits_map, List.map_ofFn, RingProgram.flat, layout, Function.comp_def]
  · simpa [coordinateRows, layout] using hd
  · intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    constructor
    · simp [leftBits_map, List.map_ofFn, RingProgram.flat, layout, Function.comp_def]
    · simpa [layout] using hd

def rowTriples {B : ℕ} (r : Row B) : List (RingScan.WordTriple B) :=
  r.2.map fun p => (r.1, p.1, p.2)

def matrixTriples {B : ℕ} (rows : List (Row B)) : List (RingScan.WordTriple B) :=
  (rows.map rowTriples).flatten

theorem tripleBits_append {B : ℕ} (xs ys : List (RingScan.WordTriple B)) :
    RingScan.tripleBits (xs ++ ys) = RingScan.tripleBits xs ++ RingScan.tripleBits ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [RingScan.tripleBits, ih, List.append_assoc]

theorem rowBits_eq_triples {B : ℕ} (x : Word B) (pairs : List (Word B × Word B)) :
    rowBits x.val pairs = RingScan.tripleBits (rowTriples (x, pairs)) := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih => simpa [rowBits, rowTriples, RingScan.tripleBits, List.append_assoc] using ih

theorem matrixBits_eq_triples {B : ℕ} (rows : List (Row B)) :
    matrixBits rows = RingScan.tripleBits (matrixTriples rows) := by
  induction rows with
  | nil => rfl
  | cons r rows ih =>
    simp only [matrixBits, matrixTriples, List.map_cons, List.flatten_cons, tripleBits_append]
    rw [rowBits_eq_triples, ih]
    rfl

theorem allTripleBits_eq_blocks {B : ℕ} (ms : List (List (Row B))) :
    allTripleBits ms = RingScan.blockBits (ms.map matrixTriples) := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [allTripleBits, RingScan.blockBits, matrixBits_eq_triples, ih]

theorem matrixTriples_coordinateRows {B d : ℕ}
    (table : Fin d → Fin d → Fin d → Word B) (x y : RingProgram.Code (Word B) d) (k : Fin d) :
    matrixTriples (coordinateRows table x y k) = RingProgram.coordinateTriples table x y k := by
  simp [matrixTriples, coordinateRows, rowTriples, List.map_ofFn,
    RingProgram.coordinateTriples, Function.comp_def]

theorem triple_encoding {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) :
    allTripleBits (matrices table x y) = RingScan.blockBits (blocks table x y) := by
  rw [allTripleBits_eq_blocks]
  simp [matrices, blocks, List.map_ofFn, matrixTriples_coordinateRows, Function.comp_def]

/-- Native expansion on the exact finite-dimensional ring table. Degree d is
runtime data, and every occurrence of x_i/y_j is physically copied/scanned. -/
theorem expansion_eval {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) (degree width : List Bool)
    (regs : Fin 2 → Bool) (hd : degree.length = d) (hw : width.length = B) :
    ∃ n ≤ expandBudget B d, ∃ regs',
      Eval expand n
        (state regs {(layout (RingProgram.flat x) (RingProgram.flat y) degree width) with table := tableEncoding table})
        (state regs' {(layout (RingProgram.flat x) (RingProgram.flat y) degree width) with xs := RingScan.blockBits (blocks table x y)}) := by
  obtain ⟨n, hn, regs', ht⟩ := expand_eval B
    (layout (RingProgram.flat x) (RingProgram.flat y) degree width) (matrices table x y)
    regs (by simpa [matrices, layout] using hd) (matrices_fit table x y degree width hd) hw
  refine ⟨n, by simpa [layout, hd] using hn, regs', ?_⟩
  simpa only [table_encoding, triple_encoding, layout] using ht

theorem expansion_native {B d : ℕ} (table : Fin d → Fin d → Fin d → Word B)
    (x y : RingProgram.Code (Word B) d) (degree width : List Bool)
    (regs : Fin 2 → Bool) (hd : degree.length = d) (hw : width.length = B) :
    ∃ regs', RunsIn program (expandBudget B d + 1)
      ((state regs {(layout (RingProgram.flat x) (RingProgram.flat y) degree width) with table := tableEncoding table}).withPC
        (some program.entry))
      ((state regs' {(layout (RingProgram.flat x) (RingProgram.flat y) degree width) with xs := RingScan.blockBits (blocks table x y)}).withPC none) := by
  obtain ⟨n, hn, regs', ht⟩ := expansion_eval table x y degree width regs hd hw
  exact ⟨regs', n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace ht 2 4⟩

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
