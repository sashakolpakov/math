import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTripleExpand

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTriple

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem rowBits_length {B : ℕ} (x : List Bool) (pairs : List (Word B × Word B)) :
    (rowBits x pairs).length = pairs.length * (x.length + 2 * B) := by
  induction pairs with
  | nil => simp [rowBits]
  | cons p pairs ih =>
      simp [rowBits, ih, p.1.property, p.2.property]
      ring

theorem matrixBits_length {B : ℕ} (s : Store) (rows : List (Row B))
    (hfit : RowsFit s rows) :
    (matrixBits rows).length = rows.length * (3 * B * s.degree.length) := by
  induction rows with
  | nil => simp [matrixBits]
  | cons r rows ih =>
    have hr := (hfit r (by simp)).2
    have hrest : RowsFit s rows := fun a ha => hfit a (by simp [ha])
    simp only [matrixBits, List.length_append, rowBits_length, r.1.property,
      ih hrest, List.length_cons, ← hr]
    ring

theorem allTripleBits_length {B : ℕ} (s : Store) (matrices : List (List (Row B)))
    (hfit : ∀ a ∈ matrices, MatrixFits s a) :
    (allTripleBits matrices).length = matrices.length * (3 * B * s.degree.length^2) := by
  induction matrices with
  | nil => simp [allTripleBits]
  | cons a matrices ih =>
    have ha := hfit a (by simp)
    have hrest : ∀ a ∈ matrices, MatrixFits s a := fun a h => hfit a (by simp [h])
    simp only [allTripleBits, List.length_append, matrixBits_length s a ha.2.2,
      ← ha.2.1, ih hrest, List.length_cons]
    ring

theorem copyK_eval (s : Store) (regs : Fin 2 → Bool) :
    Eval (copy 9 10) (7 * s.degree.length + 5)
      (state regs {s with kc := []})
      (state (readRegs regs 0 1 none) {s with kc := s.degree}) := by
  have he := copy_eval (state regs {s with kc := []}) 9 10
    (by decide) (by decide) (by decide) (by rfl)
  convert he using 1
  · simp [state, tapes]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [state, tapes, copyStacks]

theorem finish_eval (s : Store) (regs : Fin 2 → Bool) :
    Eval (transfer 3 4) (3 * s.out.length + 3)
      (state regs {s with xs := []})
      (state (readRegs regs 0 1 none) {s with out := [], xs := s.out.reverse}) := by
  have he := transfer_eval (state regs {s with xs := []}) 3 4 (by decide)
  convert he using 1
  · simp [state, tapes]
  · apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [state, tapes, transferStacks]

/-- Three nested counted scans. Degree and width are runtime stack data. -/
abbrev expand : Cmd 2 16 := .seq (copy 9 10) (.seq kScan (transfer 3 4))

/-- Explicit cubic-in-degree, linear-in-width bound, including all repeated
source copies, each coefficient scan, and the final stream reversal. -/
def expandBudget (B d : ℕ) : ℕ :=
  (7 * d + 5) + (d * (200 * (d + 1)^2 * (B + 1) + 2) + 2) + (9 * B * d^3 + 3)

theorem expand_eval (B : ℕ) (s : Store) (matrices : List (List (Row B)))
    (regs : Fin 2 → Bool) (hd : s.degree.length = matrices.length)
    (hfit : ∀ a ∈ matrices, MatrixFits s a) (hw : s.width.length = B) :
    ∃ n ≤ expandBudget B s.degree.length, ∃ regs',
      Eval expand n
        (state regs {s with table := allTableBits matrices, out := [], xs := [], ys := [], held := [], kc := [], ic := [], jc := []})
        (state regs' {s with table := [], out := [], xs := allTripleBits matrices, ys := [], held := [], kc := [], ic := [], jc := []}) := by
  let a := {s with table := allTableBits matrices, out := [], xs := [], ys := [], held := [], ic := [], jc := []}
  have hcopy := copyK_eval a regs
  obtain ⟨n, hn, r₁, hscan⟩ := kScan_eval B {s with out := []} matrices [] s.degree
    (readRegs regs 0 1 none) hd hfit hw
  simp only [List.append_nil] at hscan
  let b := {s with table := [], out := (allTripleBits matrices).reverse, xs := [], ys := [], held := [], kc := [], ic := [], jc := []}
  have hfinish := finish_eval b r₁
  dsimp only [b] at hfinish
  simp only [List.length_reverse, List.reverse_reverse] at hfinish
  have hlen : (allTripleBits matrices).length = 3 * B * s.degree.length^3 := by
    rw [allTripleBits_length s matrices hfit, ← hd]
    ring
  refine ⟨(7 * s.degree.length + 5) + (n + (3 * (allTripleBits matrices).length + 3)),
    ?_, readRegs r₁ 0 1 none, ?_⟩
  · rw [← hd] at hn
    rw [hlen]
    unfold expandBudget
    nlinarith
  · simpa [a, b, List.length_reverse, List.reverse_reverse, List.append_nil] using
      hcopy.seq (hscan.seq hfinish)

def program := compiled expand 2 4

theorem program_run (B : ℕ) (s : Store) (matrices : List (List (Row B)))
    (regs : Fin 2 → Bool) (hd : s.degree.length = matrices.length)
    (hfit : ∀ a ∈ matrices, MatrixFits s a) (hw : s.width.length = B) :
    ∃ regs', RunsIn program (expandBudget B s.degree.length + 1)
      ((state regs {s with table := allTableBits matrices, out := [], xs := [], ys := [], held := [], kc := [], ic := [], jc := []}).withPC
        (some program.entry))
      ((state regs' {s with table := [], out := [], xs := allTripleBits matrices, ys := [], held := [], kc := [], ic := [], jc := []}).withPC none) := by
  obtain ⟨n, hn, regs', ht⟩ := expand_eval B s matrices regs hd hfit hw
  exact ⟨regs', n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace ht 2 4⟩

end SubexponentialSAT.SqrtLog.RingTriple

end OAI.Algorithms
