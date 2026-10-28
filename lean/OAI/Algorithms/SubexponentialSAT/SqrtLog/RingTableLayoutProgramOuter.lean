import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingTableLayoutProgramBlock

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingTableLayout

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem kPop_eval (s : Store) (regs : Fin 2 → Bool) :
    Eval (pop 11) 1 (state regs s)
      (state (readRegs regs 0 1 s.kc.head?) {s with kc := s.kc.tail}) := by
  have h := pop_eval (state regs s) 11
  convert h using 1
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp [ state, tapes]

abbrev layoutBits (rows : List (List Bool)) (d start : ℕ) : ℕ → List Bool
  | 0 => []
  | n+1 => matrixBits rows d start d ++ layoutBits rows d (start+1) n

abbrev kLoop : Cmd 2 18 := .while 1 (.seq blockStep (pop 11))
abbrev kScan : Cmd 2 18 := .seq (pop 11) kLoop

theorem kLoop_eval (rows : List (List Bool)) (s : Store) (regs : Fin 2 → Bool)
    (count : List Bool) (C : ℕ)
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hword : s.word = []) (hindex : s.index = [])
    (hj : s.ji = []) (hcj : s.jc = []) (hi : s.ii = []) (hci : s.ic = [])
    (hcap : s.ki.length + count.length + 2*s.degree.length*s.degree.length ≤ C)
    (hv : ∀ k < count.length, ∀ i < s.degree.length, ∀ j < s.degree.length,
      s.ki.length+k+i*s.degree.length+j*s.degree.length < rows.length) :
    ∃ n ≤ count.length * (blockBudget s.width.length s.degree.length C + 2) + 1,
      ∃ rf idx, idx.length = s.ki.length + count.length ∧
      Eval kLoop n
        (state (readRegs regs 0 1 count.head?) {s with kc := count.tail})
        (state rf {s with
          kc := []
          ki := idx
          rev := (layoutBits rows s.degree.length s.ki.length count.length).reverse ++ s.rev}) := by
  induction count generalizing s regs with
  | nil =>
      refine ⟨1, by simp, readRegs regs 0 1 none, s.ki, by simp, ?_⟩
      simpa [layoutBits] using
        (Eval.while_false (body := .seq blockStep (pop 11))
          (a := state (readRegs regs 0 1 none) {s with kc := []})
          (by simp [state, readRegs_present]))
  | cons bit count ih =>
      let s1 : Store := {s with
        kc := count
        ki := false :: s.ki
        rev := (matrixBits rows s.degree.length s.ki.length s.degree.length).reverse ++ s.rev}
      have hcap0 : s.ki.length + 2*s.degree.length*s.degree.length ≤ C := by omega
      have hv0 : ∀ i < s.degree.length, ∀ j < s.degree.length,
          s.ki.length+i*s.degree.length+j*s.degree.length < rows.length := by
        intro i hi j hj
        simpa using hv 0 (by simp) i hi j hj
      obtain ⟨m, hm, r1, he⟩ := blockStep_eval rows {s with kc := count}
        (readRegs regs 0 1 (some bit)) C hp hw hword hindex hj hcj hi hci hcap0 hv0
      have he' : Eval blockStep m
          (state (readRegs regs 0 1 (some bit)) {s with kc := count}) (state r1 s1) := he
      have hr := kPop_eval s1 r1
      have hcap1 : s1.ki.length + count.length + 2*s1.degree.length*s1.degree.length ≤ C := by
        simpa [s1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcap
      have hv1 : ∀ k < count.length, ∀ i < s1.degree.length, ∀ j < s1.degree.length,
          s1.ki.length+k+i*s1.degree.length+j*s1.degree.length < rows.length := by
        intro k hk i hi j hj
        have hh := hv (k+1) (by simpa using Nat.succ_lt_succ hk) i hi j hj
        simpa [s1, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
      obtain ⟨n, hn, rf, idx, hidx, hl⟩ := ih s1 r1 hp hw hword hindex hj hcj hi hci hcap1 hv1
      have ht := Eval.while_true
        (show (state (readRegs regs 0 1 (some bit)) {s with kc := count}).regs 1 = true by
          simp [state, readRegs_present]) (he'.seq hr) hl
      refine ⟨(m+1)+n+1, ?_, rf, idx, ?_, ?_⟩
      · simp only [s1, List.length_cons] at hm hn ⊢
        nlinarith
      · simp only [s1, List.length_cons] at hidx ⊢
        omega
      · simpa only [kLoop, s1, List.head?_cons, List.tail_cons, List.length_cons,
          layoutBits, List.reverse_append, List.append_assoc] using ht

theorem kScan_eval (rows : List (List Bool)) (s : Store) (regs : Fin 2 → Bool) (C : ℕ)
    (hp : s.powers = rows.flatten)
    (hw : ∀ row ∈ rows, row.length = s.width.length)
    (hword : s.word = []) (hindex : s.index = [])
    (hj : s.ji = []) (hcj : s.jc = []) (hi : s.ii = []) (hci : s.ic = [])
    (hcap : s.ki.length+s.kc.length+2*s.degree.length*s.degree.length ≤ C)
    (hv : ∀ k < s.kc.length, ∀ i < s.degree.length, ∀ j < s.degree.length,
      s.ki.length+k+i*s.degree.length+j*s.degree.length < rows.length) :
    ∃ n ≤ s.kc.length * (blockBudget s.width.length s.degree.length C + 2) + 2,
      ∃ rf idx, idx.length = s.ki.length+s.kc.length ∧
      Eval kScan n (state regs s)
        (state rf {s with
          kc := []
          ki := idx
          rev := (layoutBits rows s.degree.length s.ki.length s.kc.length).reverse ++ s.rev}) := by
  obtain ⟨n, hn, rf, idx, hidx, he⟩ :=
    kLoop_eval rows s regs s.kc C hp hw hword hindex hj hcj hi hci hcap hv
  exact ⟨1+n, by omega, rf, idx, hidx, (kPop_eval s regs).seq he⟩

end SubexponentialSAT.SqrtLog.RingTableLayout

end OAI.Algorithms
