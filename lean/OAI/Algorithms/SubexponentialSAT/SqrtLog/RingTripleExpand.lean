import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTripleMatrix

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem xBits_length {B : ℕ} (rows : List (Row B)) :
    (xBits rows).length = rows.length * B := by
  induction rows with
  | nil => simp [xBits]
  | cons r rows ih =>
      simp only [xBits, List.length_append, ih, List.length_cons]
      rw [r.1.property]
      ring

abbrev startMatrix : Cmd 2 16 := .seq (copy 0 4) (copy 9 11)

theorem startMatrix_eval (s : Store) (regs : Fin 2 → Bool) :
    ∃ regs', Eval startMatrix (7 * s.x.length + 7 * s.degree.length + 10)
      (state regs {s with xs := [], ic := []})
      (state regs' {s with xs := s.x, ic := s.degree}) := by
  let d := state regs {s with xs := [], ic := []}
  let a := afterCopy d 0 4
  have h1 := copy_eval d 0 4 (by decide) (by decide) (by decide) (by rfl)
  have h2 := copy_eval a 9 11 (by decide) (by decide) (by decide) (by rfl)
  have hf : afterCopy a 9 11 =
      state (afterCopy a 9 11).regs {s with xs := s.x, ic := s.degree} := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [a, d, afterCopy, copyStacks, state, tapes]
  refine ⟨(afterCopy a 9 11).regs, ?_⟩
  rw [← hf]
  convert h1.seq h2 using 1
  simp [a, d, afterCopy, copyStacks, state, tapes]
  omega

def MatrixFits {B : ℕ} (s : Store) (rows : List (Row B)) : Prop :=
  xBits rows = s.x ∧ s.degree.length = rows.length ∧ RowsFit s rows

abbrev matrixStep : Cmd 2 16 := .seq startMatrix iScan

theorem matrixStep_eval (B : ℕ) (s : Store) (rows : List (Row B))
    (tail : List Bool) (regs : Fin 2 → Bool)
    (hfit : MatrixFits s rows) (hw : s.width.length = B) :
    ∃ n ≤ 200 * (s.degree.length + 1)^2 * (B + 1), ∃ regs',
      Eval matrixStep n
        (state regs {s with xs := [], ys := [], held := [], table := tableBits rows ++ tail, ic := [], jc := []})
        (state regs' {s with xs := [], ys := [], held := [], table := tail, ic := [], jc := [], out := (matrixBits rows).reverse ++ s.out}) := by
  obtain ⟨r₁, hs⟩ := startMatrix_eval
    {s with ys := [], held := [], table := tableBits rows ++ tail, jc := []} regs
  obtain ⟨n, hn, r₂, hi⟩ := iScan_eval B s rows tail s.degree r₁ hfit.2.1 hfit.2.2 hw
  refine ⟨7 * s.x.length + 7 * s.degree.length + 10 + n, ?_, r₂, ?_⟩
  · have hxl : s.x.length = s.degree.length * B := by
      rw [← hfit.1, xBits_length, ← hfit.2.1]
    rw [← hfit.2.1] at hn
    nlinarith [sq_nonneg (s.degree.length : ℤ)]
  · have hi' := hi
    rw [hfit.1] at hi'
    exact hs.seq hi'

abbrev allTableBits {B : ℕ} : List (List (Row B)) → List Bool
  | [] => []
  | a :: rest => tableBits a ++ allTableBits rest

abbrev allTripleBits {B : ℕ} : List (List (Row B)) → List Bool
  | [] => []
  | a :: rest => matrixBits a ++ allTripleBits rest

abbrev popK : Cmd 2 16 := .base (.atom (.pop 10 0 1))
abbrev kLoop : Cmd 2 16 := .while 1 (.seq matrixStep popK)
abbrev kScan : Cmd 2 16 := .seq popK kLoop

theorem popK_eval (regs : Fin 2 → Bool) (s : Store) :
    Eval popK 1 (state regs s)
      (state (readRegs regs 0 1 s.kc.head?) {s with kc := s.kc.tail}) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 2) (s := 16) 10 0 1)
    (state regs s) using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, state, tapes]

theorem kLoop_eval (B : ℕ) (s : Store) (matrices : List (List (Row B)))
    (tail count : List Bool) (regs : Fin 2 → Bool)
    (hc : count.length = matrices.length)
    (hfit : ∀ a ∈ matrices, MatrixFits s a) (hw : s.width.length = B) :
    ∃ n ≤ matrices.length * (200 * (s.degree.length + 1)^2 * (B + 1) + 2) + 1, ∃ regs',
      Eval kLoop n
        (state (readRegs regs 0 1 count.head?)
          {s with xs := [], ys := [], held := [], table := allTableBits matrices ++ tail, kc := count.tail, ic := [], jc := []})
        (state regs' {s with xs := [], ys := [], held := [], table := tail, kc := [], ic := [], jc := [], out := (allTripleBits matrices).reverse ++ s.out}) := by
  induction matrices generalizing s count regs with
  | nil =>
    have hcount : count = [] := List.length_eq_zero_iff.mp (by simpa using hc)
    subst count
    refine ⟨1, by simp, readRegs regs 0 1 none, ?_⟩
    simpa [allTableBits, allTripleBits] using
      (Eval.while_false (test := (1 : Fin 2)) (body := .seq matrixStep popK)
        (a := state (readRegs regs 0 1 none)
          {s with xs := [], ys := [], held := [], table := tail, kc := [], ic := [], jc := []})
        (by simp [state, readRegs_present]))
  | cons a matrices ih =>
    cases count with
    | nil => simp at hc
    | cons bit count =>
      have hc' : count.length = matrices.length := by simpa using hc
      have ha := hfit a (by simp)
      obtain ⟨u, hu, r₁, hstep⟩ := matrixStep_eval B {s with kc := count} a
        (allTableBits matrices ++ tail) (readRegs regs 0 1 (some bit)) ha hw
      let m := {s with xs := [], ys := [], held := [], table := allTableBits matrices ++ tail, kc := count, ic := [], jc := [], out := (matrixBits a).reverse ++ s.out}
      have hp := popK_eval r₁ m
      have hfit' : ∀ a ∈ matrices, MatrixFits m a := by
        intro a ha
        exact hfit a (by simp [ha])
      obtain ⟨n, hn, r₂, hloop⟩ := ih m count r₁ hc' hfit' hw
      have hbody : Eval (.seq matrixStep popK) (u + 1)
          (state (readRegs regs 0 1 (some bit))
            {s with xs := [], ys := [], held := [], table := allTableBits (a :: matrices) ++ tail, kc := count, ic := [], jc := []})
          (state (readRegs r₁ 0 1 count.head?) {m with kc := count.tail}) := by
        simpa [m, allTableBits, List.append_assoc] using hstep.seq hp
      refine ⟨u + 1 + n + 1, ?_, r₂, ?_⟩
      · change n ≤ matrices.length * (200 * (s.degree.length + 1)^2 * (B + 1) + 2) + 1 at hn
        change u ≤ 200 * (s.degree.length + 1)^2 * (B + 1) at hu
        simp only [List.length_cons]
        nlinarith
      · have he := Eval.while_true (test := (1 : Fin 2))
          (show (state (readRegs regs 0 1 (some bit))
            {s with xs := [], ys := [], held := [], table := allTableBits (a :: matrices) ++ tail, kc := count, ic := [], jc := []}).regs 1 = true by
              simp [state, readRegs_present]) hbody hloop
        simpa [kLoop, m, allTripleBits, List.reverse_append, List.append_assoc] using he

theorem kScan_eval (B : ℕ) (s : Store) (matrices : List (List (Row B)))
    (tail count : List Bool) (regs : Fin 2 → Bool)
    (hc : count.length = matrices.length)
    (hfit : ∀ a ∈ matrices, MatrixFits s a) (hw : s.width.length = B) :
    ∃ n ≤ matrices.length * (200 * (s.degree.length + 1)^2 * (B + 1) + 2) + 2, ∃ regs',
      Eval kScan n
        (state regs {s with xs := [], ys := [], held := [], table := allTableBits matrices ++ tail, kc := count, ic := [], jc := []})
        (state regs' {s with xs := [], ys := [], held := [], table := tail, kc := [], ic := [], jc := [], out := (allTripleBits matrices).reverse ++ s.out}) := by
  have hp := popK_eval regs {s with xs := [], ys := [], held := [], table := allTableBits matrices ++ tail, kc := count, ic := [], jc := []}
  obtain ⟨n, hn, regs', ht⟩ := kLoop_eval B s matrices tail count regs hc hfit hw
  exact ⟨1 + n, by omega, regs', hp.seq ht⟩

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
