import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-! A bounded variant of the existing unary controller rule. Its invariant
may retain registers that the actual pop instruction does not touch. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.UnaryForPrograms

variable {R S : ℕ}

theorem bounded_visits (p : Ports R S) (body : Cmd R S)
    (I : ℕ → State R S → Prop) (N C : ℕ)
    (stable : ∀ i d, I i d → I i (popped p d))
    (step : ∀ i < N, ∀ d, I i d → ∃ n e, n ≤ C ∧ Eval body n d e ∧
      e.stacks p.counter=d.stacks p.counter ∧ I (i+1) e)
    (word : List Bool) :
    ∀ i d, d.stacks p.counter=word → I i d → i+word.length ≤ N →
      ∃ costs n e, Visits p body costs n d e ∧ I (i+word.length) e ∧
        n ≤ word.length*(C+2)+2 := by
  induction word with
  | nil =>
    intro i d hd hi hN
    exact ⟨[],2,popped p d,Visits.done d hd,by simpa using stable i d hi,by simp⟩
  | cons bit word ih =>
    intro i d hd hi hN
    have hiN : i < N := by simp only [List.length_cons] at hN; omega
    obtain ⟨nb,e,hnb,hbody,hcounter,hie⟩ := step i hiN (popped p d) (stable i d hi)
    have he : e.stacks p.counter=word := by rw [hcounter,popped_counter,hd]; rfl
    have htail : i+1+word.length ≤ N := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hN
    obtain ⟨costs,nt,f,ht,hif,hnt⟩ := ih (i+1) e he hie htail
    refine ⟨nb::costs,nb+nt+2,f,Visits.step (by simp [hd]) hbody hcounter ht,?_,?_⟩
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hif
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

theorem bounded_for_eval (p : Ports R S) (body : Cmd R S)
    (I : ℕ → State R S → Prop) (N C : ℕ)
    (stable : ∀ i d, I i d → I i (popped p d))
    (step : ∀ i < N, ∀ d, I i d → ∃ n e, n ≤ C ∧ Eval body n d e ∧
      e.stacks p.counter=d.stacks p.counter ∧ I (i+1) e)
    (d : State R S) (hd : (d.stacks p.counter).length=N) (hi : I 0 d) :
    ∃ n e, Eval (forCmd p body) n d e ∧ I N e ∧ e.stacks p.counter=[] ∧ n ≤ N*(C+2)+2 := by
  obtain ⟨costs,n,e,hvis,hei,hn⟩ := bounded_visits p body I N C stable step
    (d.stacks p.counter) 0 d rfl hi (by omega)
  refine ⟨n,e,hvis.eval,?_,hvis.bounds.2.1,?_⟩
  · simpa [hd] using hei
  · simpa [hd] using hn

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
