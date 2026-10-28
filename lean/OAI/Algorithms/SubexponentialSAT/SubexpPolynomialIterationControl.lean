import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialServiceControl
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-! Reusing the polynomial multiplication workspace in a runtime-counted
loop. The output on 244 is moved back to accumulator 240, with all temporary
bits erased. The loop itself is the verified unary controller. -/

namespace SubexponentialSAT.SubexpPolynomialIterationControl

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpPolynomialServiceControl (transfer transfer_run)

def commit : Code := .seq (clear 240) (.seq (transfer 244 245) (transfer 245 240))

theorem commit_run (s : Store) (out : List Bool) (h244 : s 244 = []) (h245 : s 245 = []) :
    ExecutesIn commit (2 * (s 240).length + 6 * out.length + 9)
      (Function.update s 244 out) (Function.update s 240 out) := by
  let s₁ := Function.update (Function.update s 244 out) 240 []
  let s₂ := Function.update (Function.update s 240 []) 245 out.reverse
  have h₁ : ExecutesIn (clear 240) (2 * (s 240).length + 3)
      (Function.update s 244 out) s₁ := by
    simpa [s₁] using clear_run 240 (Function.update s 244 out)
  have he₂ : Function.update (Function.update s₁ 244 []) 245
      ((s₁ 244).reverse ++ s₁ 245) = s₂ := by
    funext j
    by_cases h : j = 244 <;> simp [s₁, s₂, h, h244, h245, Function.update_apply]
  have h₂ : ExecutesIn (transfer 244 245) (3 * out.length + 3) s₁ s₂ := by
    have h := transfer_run 244 245 s₁ (by decide)
    rw [he₂] at h
    simpa [s₁] using h
  have he₃ : Function.update (Function.update s₂ 245 []) 240
      ((s₂ 245).reverse ++ s₂ 240) = Function.update s 240 out := by
    funext j
    by_cases h : j = 245 <;> by_cases h240 : j = 240 <;>
      simp [s₂, h, h240, h245 ]
  have h₃ : ExecutesIn (transfer 245 240) (3 * out.length + 3) s₂
      (Function.update s 240 out) := by
    have h := transfer_run 245 240 s₂ (by decide)
    rw [he₃] at h
    simpa [s₂] using h
  have h := h₁.seq (h₂.seq h₃)
  convert h using 1
  all_goals first | rfl | ring

def step (service : Code) : Code := .seq service commit

theorem step_run (service : Code) (K : ℕ) (s : Store) (out : List Bool)
    (h244 : s 244 = []) (h245 : s 245 = [])
    (hservice : ExecutesIn service K s (Function.update s 244 out)) :
    ExecutesIn (step service) (K + 2 * (s 240).length + 6 * out.length + 9)
      s (Function.update s 240 out) := by
  have h := hservice.seq (commit_run s out h244 h245)
  convert h using 1
  all_goals first | rfl | ring

def counterPorts : UnaryForPrograms.Ports 16 256 := ⟨246, 0, 1⟩
def repeatLoop (iteration : Code) : Code := UnaryForPrograms.forCmd counterPorts iteration

abbrev ready {S : Type*} (base : Store) (encode : S → List Bool) (a : S)
    (counter : List Bool) : Store :=
  Function.update (Function.update base 240 (encode a)) 246 counter

abbrev state {S : Type*} (base : Store) (encode : S → List Bool) (regs : Fin 16 → Bool)
    (a : S) (counter : List Bool) : Data := ⟨regs, ready base encode a counter⟩

theorem popped_state {S : Type*} (base : Store) (encode : S → List Bool)
    (regs : Fin 16 → Bool) (a : S) (counter : List Bool) :
    UnaryForPrograms.popped counterPorts (state base encode regs a counter) =
      state base encode (readRegs regs 0 1 counter.head?) a counter.tail := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · simp [UnaryForPrograms.popped, ready, counterPorts]

/-- Exact observations of every invocation of the fixed iteration command.
The only component premise is its actual instruction trace and cost. -/
theorem repeat_visits {S : Type*} (base : Store) (encode : S → List Bool)
    (iteration : Code) (f : S → S) (K : ℕ)
    (hstep : ∀ a counter, ExecutesIn iteration K (ready base encode a counter)
      (ready base encode (f a) counter)) (counter : List Bool) :
    ∀ (regs : Fin 16 → Bool) (a : S), ∃ costs n regs',
      UnaryForPrograms.Visits counterPorts iteration costs n
        (state base encode regs a counter)
        (state base encode regs' ((f^[counter.length]) a) []) ∧
      n ≤ counter.length * (K + 2) + 2 := by
  induction counter with
  | nil =>
      intro regs a
      refine ⟨[], 2, readRegs regs 0 1 none, ?_, by simp⟩
      simpa only [popped_state, List.head?_nil, List.tail_nil, List.length_nil,
        Function.iterate_zero_apply] using
        UnaryForPrograms.Visits.done (p := counterPorts) (body := iteration)
          (state base encode regs a []) rfl
  | cons bit counter ih =>
      intro regs a
      obtain ⟨nb, rb, hnb, hb⟩ := hstep a counter (readRegs regs 0 1 (some bit))
      obtain ⟨costs, nt, rt, ht, hnt⟩ := ih rb (f a)
      refine ⟨nb :: costs, nb + nt + 2, rt, ?_, ?_⟩
      · have h := UnaryForPrograms.Visits.step
          (p := counterPorts) (body := iteration)
          (d := state base encode regs a (bit :: counter))
          (by simp [ ready, counterPorts])
          (by simpa only [popped_state, List.head?_cons, List.tail_cons] using hb)
          (by simp [ ready, counterPorts, UnaryForPrograms.popped]) ht
        simpa only [List.length_cons, Function.iterate_succ_apply] using h
      · simp only [List.length_cons]
        nlinarith

theorem repeat_run {S : Type*} (base : Store) (encode : S → List Bool)
    (iteration : Code) (f : S → S) (K : ℕ)
    (hstep : ∀ a counter, ExecutesIn iteration K (ready base encode a counter)
      (ready base encode (f a) counter)) (counter : List Bool) (a : S) :
    ExecutesIn (repeatLoop iteration) (counter.length * (K + 2) + 2)
      (ready base encode a counter) (ready base encode ((f^[counter.length]) a) []) := by
  intro regs
  obtain ⟨costs, n, regs', hv, hn⟩ := repeat_visits base encode iteration f K hstep counter regs a
  exact ⟨n, regs', hn, hv.eval⟩

end SubexponentialSAT.SubexpPolynomialIterationControl

end OAI.Algorithms
