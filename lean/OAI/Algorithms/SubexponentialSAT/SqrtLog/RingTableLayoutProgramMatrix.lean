import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayoutProgramRowStep

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem iPop_eval (s : Store) (regs : Fin 2 → Bool) :
    Eval (pop 12) 1 (state regs s)
      (state (readRegs regs 0 1 s.ic.head?) {s with ic := s.ic.tail}) := by
  have h := pop_eval (state regs s) 12
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [ state, tapes]

abbrev matrixBits (rows : List (List Bool)) (d start : ℕ) : ℕ → List Bool
  | 0 => []
  | n+1 => rowBits rows d start d ++ matrixBits rows d (start+d) n

abbrev iLoop : Cmd 2 18 := .while 1 (.seq rowStep (pop 12))
abbrev iScan : Cmd 2 18 := .seq (pop 12) iLoop

theorem iLoop_eval (rows : List (List Bool)) (s : Store) (regs : Fin 2 → Bool)
    (count : List Bool) (C : ℕ)
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hword : s.word = []) (hindex : s.index = []) (hj : s.ji = []) (hc : s.jc = [])
    (hcap : s.ii.length + count.length*s.degree.length + s.degree.length*s.degree.length ≤ C)
    (hv : ∀ i < count.length, ∀ j < s.degree.length,
      s.ii.length + i*s.degree.length + j*s.degree.length < rows.length) :
    ∃ n ≤ count.length * (rowBudget s.width.length s.degree.length C + 2) + 1,
      ∃ rf idx, idx.length = s.ii.length + count.length*s.degree.length ∧
      Eval iLoop n
        (state (readRegs regs 0 1 count.head?) {s with ic := count.tail})
        (state rf {s with
          ic := []
          ii := idx
          rev := (matrixBits rows s.degree.length s.ii.length count.length).reverse ++ s.rev}) := by
  induction count generalizing s regs with
  | nil =>
      refine ⟨1, by simp, readRegs regs 0 1 none, s.ii, by simp, ?_⟩
      simpa [matrixBits] using
        (Eval.while_false (body := .seq rowStep (pop 12))
          (a := state (readRegs regs 0 1 none) {s with ic := []})
          (by simp [state, readRegs_present]))
  | cons bit count ih =>
      let s1 : Store := {s with
        ic := count
        ii := s.degree ++ s.ii
        rev := (rowBits rows s.degree.length s.ii.length s.degree.length).reverse ++ s.rev}
      have hcap0 : s.ii.length + s.degree.length*s.degree.length ≤ C := by omega
      have hv0 : ∀ j < s.degree.length, s.ii.length+j*s.degree.length < rows.length := by
        intro j hj
        simpa using hv 0 (by simp) j hj
      obtain ⟨m, hm, r1, he⟩ := rowStep_eval rows {s with ic := count}
        (readRegs regs 0 1 (some bit)) C hp hw hword hindex hj hc hcap0 hv0
      have he' : Eval rowStep m
          (state (readRegs regs 0 1 (some bit)) {s with ic := count}) (state r1 s1) := he
      have hr := iPop_eval s1 r1
      have hcap1 : s1.ii.length + count.length*s1.degree.length +
          s1.degree.length*s1.degree.length ≤ C := by
        simp only [s1, List.length_append, List.length_cons] at hcap ⊢
        nlinarith
      have hv1 : ∀ i < count.length, ∀ j < s1.degree.length,
          s1.ii.length+i*s1.degree.length+j*s1.degree.length < rows.length := by
        intro i hi j hj
        have hh := hv (i+1) (by simpa using Nat.succ_lt_succ hi) j hj
        simp only [s1, List.length_append] at ⊢
        nlinarith
      obtain ⟨n, hn, rf, idx, hidx, hl⟩ := ih s1 r1 hp hw hword hindex hj hc hcap1 hv1
      have ht := Eval.while_true
        (show (state (readRegs regs 0 1 (some bit)) {s with ic := count}).regs 1 = true by
          simp [state, readRegs_present]) (he'.seq hr) hl
      refine ⟨(m+1)+n+1, ?_, rf, idx, ?_, ?_⟩
      · simp only [s1, List.length_cons] at hm hn ⊢
        nlinarith
      · simp only [s1, List.length_append, List.length_cons] at hidx ⊢
        nlinarith
      · simpa only [iLoop, s1, List.head?_cons, List.tail_cons, List.length_cons,
          List.length_append, matrixBits, Nat.add_comm, List.reverse_append, List.append_assoc]
          using ht

theorem iScan_eval (rows : List (List Bool)) (s : Store) (regs : Fin 2 → Bool) (C : ℕ)
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hword : s.word = []) (hindex : s.index = []) (hj : s.ji = []) (hc : s.jc = [])
    (hcap : s.ii.length + s.ic.length*s.degree.length + s.degree.length*s.degree.length ≤ C)
    (hv : ∀ i < s.ic.length, ∀ j < s.degree.length,
      s.ii.length+i*s.degree.length+j*s.degree.length < rows.length) :
    ∃ n ≤ s.ic.length * (rowBudget s.width.length s.degree.length C + 2) + 2,
      ∃ rf idx, idx.length = s.ii.length + s.ic.length*s.degree.length ∧
      Eval iScan n (state regs s)
        (state rf {s with
          ic := []
          ii := idx
          rev := (matrixBits rows s.degree.length s.ii.length s.ic.length).reverse ++ s.rev}) := by
  obtain ⟨n, hn, rf, idx, hidx, he⟩ :=
    iLoop_eval rows s regs s.ic C hp hw hword hindex hj hc hcap hv
  exact ⟨1+n, by omega, rf, idx, hidx, (iPop_eval s regs).seq he⟩

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
