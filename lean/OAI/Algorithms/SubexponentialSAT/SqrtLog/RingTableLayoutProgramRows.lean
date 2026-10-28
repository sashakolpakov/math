import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayoutProgramStep

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev pop (port : Fin 18) : Cmd 2 18 := .base (.atom (.pop port 0 1))
def afterPop (d : Data) (port : Fin 18) : Data :=
  ⟨readRegs d.regs 0 1 (d.stacks port).head?,
    Function.update d.stacks port (d.stacks port).tail⟩

theorem pop_eval (d : Data) (port : Fin 18) : Eval (pop port) 1 d (afterPop d port) :=
  .base (.atom _ _)

theorem jPop_eval (s : Store) (regs : Fin 2 → Bool) :
    Eval (pop 13) 1 (state regs s)
      (state (readRegs regs 0 1 s.jc.head?) {s with jc := s.jc.tail}) := by
  have h := pop_eval (state regs s) 13
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [ state, tapes]

def rowBits (rows : List (List Bool)) (d start : ℕ) : ℕ → List Bool
  | 0 => []
  | n+1 => wordAt rows start ++ rowBits rows d (start+d) n

def emitBudget (B d C : ℕ) : ℕ := C * (14*B+17) + 18*B + 7*d + 29
abbrev jLoop : Cmd 2 18 := .while 1 (.seq emit (pop 13))
abbrev jScan : Cmd 2 18 := .seq (pop 13) jLoop

theorem jLoop_eval (rows : List (List Bool)) (s : Store) (regs : Fin 2 → Bool)
    (count : List Bool) (C : ℕ)
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hword : s.word = []) (hindex : s.index = [])
    (hcap : s.ji.length + count.length * s.degree.length ≤ C)
    (hv : ∀ j < count.length, s.ji.length + j*s.degree.length < rows.length) :
    ∃ n ≤ count.length * (emitBudget s.width.length s.degree.length C + 2) + 1,
      ∃ rf idx, idx.length = s.ji.length + count.length*s.degree.length ∧
      Eval jLoop n
        (state (readRegs regs 0 1 count.head?) {s with jc := count.tail})
        (state rf {s with
          jc := []
          ji := idx
          rev := (rowBits rows s.degree.length s.ji.length count.length).reverse ++ s.rev}) := by
  induction count generalizing s regs with
  | nil =>
      refine ⟨1, by simp, readRegs regs 0 1 none, s.ji, by simp, ?_⟩
      simpa [rowBits, jLoop] using
        (Eval.while_false (body := .seq emit (pop 13))
          (a := state (readRegs regs 0 1 none) {s with jc := []})
          (by simp [state, readRegs_present]))
  | cons bit count ih =>
      let s1 : Store := {s with
        jc := count
        ji := s.degree ++ s.ji
        rev := (wordAt rows s.ji.length).reverse ++ s.rev}
      have hb : s.ji.length < rows.length := by simpa using hv 0 (by simp)
      obtain ⟨r1, he⟩ := emit_eval {s with jc := count}
        (readRegs regs 0 1 (some bit)) rows hp hw hb hword hindex
      have he' : Eval emit
          (s.ji.length * (14*s.width.length+17) + 18*s.width.length + 7*s.degree.length + 29)
          (state (readRegs regs 0 1 (some bit)) {s with jc := count})
          (state r1 s1) := he
      have hr := jPop_eval s1 r1
      have hcap1 : s1.ji.length + count.length*s1.degree.length ≤ C := by
        simp only [s1, List.length_append, List.length_cons] at hcap ⊢
        nlinarith
      have hv1 : ∀ j < count.length,
          s1.ji.length + j*s1.degree.length < rows.length := by
        intro j hj
        have hh := hv (j+1) (by simpa using Nat.succ_lt_succ hj)
        simp only [s1, List.length_append] at ⊢
        nlinarith
      obtain ⟨n, hn, rf, idx, hidx, hl⟩ := ih s1 r1 hp hw hword hindex hcap1 hv1
      have ht := Eval.while_true
        (show (state (readRegs regs 0 1 (some bit)) {s with jc := count}).regs 1 = true by
          simp [state, readRegs_present]) (he'.seq hr) hl
      refine ⟨(s.ji.length * (14*s.width.length+17) + 18*s.width.length +
        7*s.degree.length + 29 + 1) + n + 1, ?_, rf, idx, ?_, ?_⟩
      · have hstart : s.ji.length ≤ C := by omega
        simp only [s1, List.length_cons] at hn ⊢
        dsimp [emitBudget] at hn ⊢
        nlinarith
      · simp only [s1, List.length_append, List.length_cons] at hidx ⊢
        nlinarith
      · simpa only [jLoop, s1, List.head?_cons, List.tail_cons, List.length_cons,
          List.length_append, rowBits, Nat.add_comm, List.reverse_append, List.append_assoc]
          using ht

theorem jScan_eval (rows : List (List Bool)) (s : Store) (regs : Fin 2 → Bool) (C : ℕ)
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hword : s.word = []) (hindex : s.index = [])
    (hcap : s.ji.length + s.jc.length*s.degree.length ≤ C)
    (hv : ∀ j < s.jc.length, s.ji.length + j*s.degree.length < rows.length) :
    ∃ n ≤ s.jc.length * (emitBudget s.width.length s.degree.length C + 2) + 2,
      ∃ rf idx, idx.length = s.ji.length + s.jc.length*s.degree.length ∧
      Eval jScan n (state regs s)
        (state rf {s with
          jc := []
          ji := idx
          rev := (rowBits rows s.degree.length s.ji.length s.jc.length).reverse ++ s.rev}) := by
  obtain ⟨n, hn, rf, idx, hidx, he⟩ := jLoop_eval rows s regs s.jc C hp hw hword hindex hcap hv
  exact ⟨1+n, by omega, rf, idx, hidx, (jPop_eval s regs).seq he⟩

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
