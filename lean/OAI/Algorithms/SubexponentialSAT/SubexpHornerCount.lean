import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpHornerControl

namespace OAI.Algorithms

/-! Horner control with an arbitrary unary count word. Only its length is
used; callers need not rewrite true bits to false bits. -/

namespace SubexponentialSAT.SubexpHornerControl

open BitProgram StructuredCalls

def countedWords {C : Type*} (encode : C → List Bool) (base : Words)
    (cs : List C) (a : C) (count : List Bool) : Words :=
  { readyWords encode base cs a with shape := count }

theorem loop_count_eval {C : Type*} (encode : C → List Bool) (base : Words)
    (iteration : Cmd 8 87) (step : C → C → C) (K : ℕ)
    (hstep : ∀ regs cs a c count,
      ∃ n ≤ K, ∃ regs', Eval iteration n
        (state regs (countedWords encode base (c :: cs) a count))
        (state regs' (countedWords encode base cs (step a c) count)))
    (cs : List C) (a : C) (count : List Bool) (hlen : count.length = cs.length)
    (regs : Fin 8 → Bool) :
    ∃ n ≤ cs.length * (K + 2) + 1, ∃ regs',
      Eval (.while 1 (.seq iteration popShape)) n
        (state (readRegs regs 0 1 count.head?)
          (countedWords encode base cs a count.tail))
        (state regs' (readyWords encode base [] (fold step cs a))) := by
  induction cs generalizing a count regs with
  | nil =>
      have hc : count = [] := List.length_eq_zero_iff.mp hlen
      subst count
      refine ⟨1, by simp, readRegs regs 0 1 none, ?_⟩
      exact Eval.while_false (by simp [state, readRegs])
  | cons c cs ih =>
      cases count with
      | nil => simp at hlen
      | cons b count =>
          have hlen' : count.length = cs.length := by simpa using hlen
          obtain ⟨n, hn, r1, h1⟩ := hstep (readRegs regs 0 1 (some b)) cs a c count
          have hp := popShape_eval r1 (countedWords encode base cs (step a c) count)
          obtain ⟨m, hm, r2, h2⟩ := ih (step a c) count hlen' r1
          have hh := Eval.while_true (by simp [state, readRegs]) (h1.seq hp) h2
          refine ⟨n + 1 + m + 1, ?_, r2, ?_⟩
          · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
          · simpa [countedWords, readyWords, fold, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using hh

theorem command_count_eval {C : Type*} (encode : C → List Bool) (base : Words)
    (iteration : Cmd 8 87) (step : C → C → C) (K : ℕ)
    (hstep : ∀ regs cs a c count,
      ∃ n ≤ K, ∃ regs', Eval iteration n
        (state regs (countedWords encode base (c :: cs) a count))
        (state regs' (countedWords encode base cs (step a c) count)))
    (cs : List C) (a : C) (count : List Bool) (hlen : count.length = cs.length)
    (regs : Fin 8 → Bool) :
    ∃ n ≤ cs.length * (K + 2) + 2, ∃ regs',
      Eval (command iteration) n (state regs (countedWords encode base cs a count))
        (state regs' (readyWords encode base [] (fold step cs a))) := by
  have hp := popShape_eval regs (countedWords encode base cs a count)
  obtain ⟨n, hn, rf, hr⟩ := loop_count_eval encode base iteration step K hstep cs a count hlen regs
  exact ⟨1 + n, by omega, rf, hp.seq hr⟩

end SubexponentialSAT.SubexpHornerControl

end OAI.Algorithms
