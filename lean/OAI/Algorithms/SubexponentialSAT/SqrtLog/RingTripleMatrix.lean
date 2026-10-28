import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTripleRowStep

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpQuarticRing

abbrev Row (B : ℕ) := Word B × List (Word B × Word B)

def xBits {B : ℕ} : List (Row B) → List Bool
  | [] => []
  | r :: rs => r.1.val ++ xBits rs

def tableBits {B : ℕ} : List (Row B) → List Bool
  | [] => []
  | r :: rs => rightBits r.2 ++ tableBits rs

def matrixBits {B : ℕ} : List (Row B) → List Bool
  | [] => []
  | r :: rs => rowBits r.1.val r.2 ++ matrixBits rs

def RowsFit {B : ℕ} (s : Store) (rows : List (Row B)) : Prop :=
  ∀ r ∈ rows, leftBits r.2 = s.y ∧ s.degree.length = r.2.length

abbrev popI : Cmd 2 16 := .base (.atom (.pop 11 0 1))
abbrev iLoop : Cmd 2 16 := .while 1 (.seq rowStep popI)
abbrev iScan : Cmd 2 16 := .seq popI iLoop

theorem popI_eval (regs : Fin 2 → Bool) (s : Store) :
    Eval popI 1 (state regs s)
      (state (readRegs regs 0 1 s.ic.head?) {s with ic := s.ic.tail}) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 2) (s := 16) 11 0 1)
    (state regs s) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, state, tapes]

theorem iLoop_eval (B : ℕ) (s : Store) (rows : List (Row B))
    (tail count : List Bool) (regs : Fin 2 → Bool)
    (hc : count.length = rows.length) (hfit : RowsFit s rows) (hw : s.width.length = B) :
    ∃ n ≤ rows.length * (100 * (s.degree.length + 1) * (B + 1) + 2) + 1, ∃ regs',
      Eval iLoop n
        (state (readRegs regs 0 1 count.head?)
          {s with xs := xBits rows, ys := [], held := [], table := tableBits rows ++ tail, ic := count.tail, jc := []})
        (state regs' {s with xs := [], ys := [], held := [], table := tail, ic := [], jc := [], out := (matrixBits rows).reverse ++ s.out}) := by
  induction rows generalizing s count regs with
  | nil =>
    have hcount : count = [] := List.length_eq_zero_iff.mp (by simpa using hc)
    subst count
    refine ⟨1, by simp, readRegs regs 0 1 none, ?_⟩
    simpa [xBits, tableBits, matrixBits] using
      (Eval.while_false (test := (1 : Fin 2)) (body := .seq rowStep popI)
        (a := state (readRegs regs 0 1 none)
          {s with xs := [], ys := [], held := [], table := tail, ic := [], jc := []})
        (by simp [state, readRegs_present]))
  | cons r rows ih =>
    cases count with
    | nil => simp at hc
    | cons bit count =>
      have hc' : count.length = rows.length := by simpa using hc
      have hrow := hfit r (by simp)
      obtain ⟨u, hu, r₁, hrowstep⟩ := rowStep_eval B {s with ic := count}
        (readRegs regs 0 1 (some bit)) r.1 r.2 (xBits rows) (tableBits rows ++ tail)
        hrow.1 hrow.2 hw
      let m := {s with xs := xBits rows, ys := [], held := [], table := tableBits rows ++ tail, ic := count, jc := [], out := (rowBits r.1.val r.2).reverse ++ s.out}
      have hp := popI_eval r₁ m
      have hfit' : RowsFit m rows := by
        intro a ha
        exact hfit a (by simp [ha])
      obtain ⟨n, hn, r₂, hloop⟩ := ih m count r₁ hc' hfit' hw
      have hbody : Eval (.seq rowStep popI) (u + 1)
          (state (readRegs regs 0 1 (some bit))
            {s with xs := xBits (r :: rows), ys := [], held := [], table := tableBits (r :: rows) ++ tail, ic := count, jc := []})
          (state (readRegs r₁ 0 1 count.head?) {m with ic := count.tail}) := by
        simpa [m, xBits, tableBits, List.append_assoc] using hrowstep.seq hp
      refine ⟨u + 1 + n + 1, ?_, r₂, ?_⟩
      · change n ≤ rows.length * (100 * (s.degree.length + 1) * (B + 1) + 2) + 1 at hn
        change u ≤ 100 * (s.degree.length + 1) * (B + 1) at hu
        simp only [List.length_cons]
        nlinarith
      · have he := Eval.while_true (test := (1 : Fin 2))
          (show (state (readRegs regs 0 1 (some bit))
            {s with xs := xBits (r :: rows), ys := [], held := [], table := tableBits (r :: rows) ++ tail, ic := count, jc := []}).regs 1 = true by
              simp [state, readRegs_present]) hbody hloop
        simpa [iLoop, m, matrixBits, List.reverse_append, List.append_assoc] using he

theorem iScan_eval (B : ℕ) (s : Store) (rows : List (Row B))
    (tail count : List Bool) (regs : Fin 2 → Bool)
    (hc : count.length = rows.length) (hfit : RowsFit s rows) (hw : s.width.length = B) :
    ∃ n ≤ rows.length * (100 * (s.degree.length + 1) * (B + 1) + 2) + 2, ∃ regs',
      Eval iScan n
        (state regs {s with xs := xBits rows, ys := [], held := [], table := tableBits rows ++ tail, ic := count, jc := []})
        (state regs' {s with xs := [], ys := [], held := [], table := tail, ic := [], jc := [], out := (matrixBits rows).reverse ++ s.out}) := by
  have hp := popI_eval regs {s with xs := xBits rows, ys := [], held := [], table := tableBits rows ++ tail, ic := count, jc := []}
  obtain ⟨n, hn, regs', ht⟩ := iLoop_eval B s rows tail count regs hc hfit hw
  exact ⟨1 + n, by omega, regs', hp.seq ht⟩

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
