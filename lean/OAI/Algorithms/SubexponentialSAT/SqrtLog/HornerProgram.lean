import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgramLoop

namespace OAI.Algorithms

/-! Exact native evaluation of a dynamically sized dense polynomial. Input
coefficients are in increasing degree order. Every other persistent stack is
preserved; the input stream and runtime counter are consumed. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec serviceSpec_frame lowFrame_refl lowFrame_update)

def encodePolynomial {C : Type*} (encode : C → List Bool) (P : List C) : List Bool :=
  P.flatMap encode

theorem encodePolynomial_length {C : Type*} (encode : C → List Bool) (W : ℕ)
    (hw : ∀ a, (encode a).length = W) (P : List C) :
    (encodePolynomial encode P).length = P.length * W := by
  induction P with
  | nil => simp [encodePolynomial]
  | cons c P ih => simp [encodePolynomial, hw, Nat.add_mul, Nat.add_comm]

theorem reverse_encodePolynomial {C : Type*} (encode : C → List Bool) (P : List C) :
    (encodePolynomial encode P).reverse = backward encode P.reverse := by
  simpa only [encodePolynomial, backward, SubexpHornerControl.backward, Function.comp_def]
    using (List.reverse_flatMap (l := P) (f := encode))

def reverseStream : Code :=
  .call (StackRoutines.reverseProgram 246 251 252 (0 : Fin 16) 1)

def command (multiply add : Code) : Code :=
  .seq reverseStream (traversal (iteration multiply add))

def budget (n W Km Ka : ℕ) : ℕ := n * (Km + Ka + 59 * W + 49) + 9

abbrev program (multiply add : Code) : Program 16 256 (size (command multiply add) + 1) :=
  compiled (command multiply add) 246 240

theorem budget_polynomial (n W Km Ka : ℕ) :
    budget n W Km Ka ≤ 60 * (n + 1) * (Km + Ka + W + 1) := by
  unfold budget
  nlinarith

/-- This is a concrete finite-command execution statement, not an arithmetic
oracle. Its only component premises are exact execution contracts for the two
fixed native binary services. -/
theorem command_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length = W)
    (P : List C) (x seed : C)
    (hP : base 246 = encodePolynomial encode P) (hx : base 247 = encode x)
    (hseed : base 240 = encode seed) (hcount : (base 248).length = P.length)
    (hw : (base 250).length = W)
    (h120 : base 120 = []) (h241 : base 241 = []) (h244 : base 244 = [])
    (h245 : base 245 = []) (h251 : base 251 = []) (h252 : base 252 = []) :
    ExecutesIn (command multiply add) (budget P.length W Km Ka) base
      (Function.update (Function.update (Function.update base 246 [])
        240 (encode (fold (stepValue mulOp addOp x) P.reverse seed))) 248 []) := by
  let s := Function.update base 246 (backward encode P.reverse)
  have hr : ExecutesIn reverseStream (9 * (P.length * W) + 7) base s := by
    intro regs
    have h := reverse_eval (⟨regs, base⟩ : Data) 246 251 252 0 1
      (by decide) (by decide) (by decide) (by decide) h251 h252
    refine ⟨9 * (base 246).length + 7, readRegs regs 0 1 none, ?_, ?_⟩
    · rw [hP, encodePolynomial_length encode W hwidth]
    · simpa [reverseStream, afterReverse, StackRoutines.reverseStacks, s, hP,
        reverse_encodePolynomial] using h
  have hs := lowFrame_update (lowFrame_refl base) 246 (by decide) (backward encode P.reverse)
  have hloop := streaming_run s encode multiply add mulOp addOp Km Ka W
    (serviceSpec_frame hm hs) (serviceSpec_frame ha hs) hwidth x
    (by simp [s, hx]) (by simp [s, hw]) (by simp [s, h120])
    (by simp [s, h241]) (by simp [s, h244]) (by simp [s, h245])
    (by simp [s, h251]) (by simp [s, h252]) P.reverse seed (base 248)
    (by simpa using hcount)
  have hin : ready s encode P.reverse seed (base 248) = s := by
    funext i
    by_cases h240 : i = 240 <;> by_cases h246 : i = 246 <;> by_cases h248 : i = 248 <;>
      simp [ready, s, h240, h246, h248, hseed]
  have hout : ready s encode [] (fold (stepValue mulOp addOp x) P.reverse seed) [] =
      Function.update (Function.update (Function.update base 246 [])
        240 (encode (fold (stepValue mulOp addOp x) P.reverse seed))) 248 [] := by
    simp [ready, s, backward, SubexpHornerControl.backward]
  rw [hin, hout] at hloop
  have h := hr.seq hloop
  have hcost : (9 * (P.length * W) + 7) +
      (P.reverse.length * (Km + Ka + 50 * W + 49) + 2) =
      budget P.length W Km Ka := by
    simp only [List.length_reverse, budget]
    ring
  simpa only [command, hcost] using h

/-- Compilation gives an actual fixed BitProgram with one final halt step. -/
theorem program_run {C : Type*} (base : Store) (encode : C → List Bool)
    (multiply add : Code) (mulOp addOp : C → C → C) (Km Ka W : ℕ)
    (hm : ServiceSpec base encode multiply mulOp Km)
    (ha : ServiceSpec base encode add addOp Ka)
    (hwidth : ∀ a, (encode a).length = W)
    (P : List C) (x seed : C)
    (hP : base 246 = encodePolynomial encode P) (hx : base 247 = encode x)
    (hseed : base 240 = encode seed) (hcount : (base 248).length = P.length)
    (hw : (base 250).length = W)
    (h120 : base 120 = []) (h241 : base 241 = []) (h244 : base 244 = [])
    (h245 : base 245 = []) (h251 : base 251 = []) (h252 : base 252 = [])
    (regs : Fin 16 → Bool) :
    ∃ rf, RunsIn (program multiply add) (budget P.length W Km Ka + 1)
      ((⟨regs, base⟩ : Data).withPC (some (program multiply add).entry))
      ((⟨rf, Function.update (Function.update (Function.update base 246 [])
        240 (encode (fold (stepValue mulOp addOp x) P.reverse seed))) 248 []⟩ : Data).withPC none) := by
  obtain ⟨n, rf, hn, h⟩ := command_run base encode multiply add mulOp addOp Km Ka W
    hm ha hwidth P x seed hP hx hseed hcount hw h120 h241 h244 h245 h251 h252 regs
  exact ⟨rf, n + 1, Nat.add_le_add_right hn 1, compiled_halt_trace h 246 240⟩

section Semantics
variable {C A : Type*} [CommRing A]

theorem fold_decode (decode : C → A) (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (x : C) (cs : List C) (seed : C) :
    decode (fold (stepValue mulOp addOp x) cs seed) =
      cs.foldl (fun value b => value * decode x + decode b) (decode seed) := by
  induction cs generalizing seed with
  | nil => rfl
  | cons c cs ih =>
      change decode (fold (stepValue mulOp addOp x) cs (stepValue mulOp addOp x seed c)) = _
      rw [ih, List.foldl_cons]
      simp only [stepValue, ha, hm]

theorem output_decode (decode : C → A) (mulOp addOp : C → C → C)
    (hm : ∀ a b, decode (mulOp a b) = decode a * decode b)
    (ha : ∀ a b, decode (addOp a b) = decode a + decode b)
    (P : List C) (x zero : C) (hz : decode zero = 0) :
    decode (fold (stepValue mulOp addOp x) P.reverse zero) =
      (PolynomialAlgorithm.denote (P.map decode)).eval (decode x) := by
  rw [fold_decode decode mulOp addOp hm ha, List.foldl_reverse, hz]
  induction P with
  | nil => simp []
  | cons a P ih =>
      simp only [List.foldr_cons, List.map_cons, PolynomialAlgorithm.denote,
        Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, ih]
      ring

end Semantics
end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
