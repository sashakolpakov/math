import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionOuter
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Actual finite-program execution of the padded triangular convolution.
The generic local pair contract is instantiated separately by the concrete
quartic multiplier and persistent-cell update service. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

variable {C : Type*}

def finishedBuffers (w : Buffers) (result : List Bool) : Buffers :=
  Function.update (Function.update (Function.update (Function.update w 0 []) 2 result) 4 []) 5 []

def convolutionBudget (D W pairCost : ℕ) : ℕ :=
  D * (outerCost D W pairCost + 4) + 5

/-- The concrete pair service yields a fixed-degree polynomial in the
runtime array dimension and coefficient width, including the final halt. -/
theorem convolutionBudget_quartic_le (D B : ℕ) :
    convolutionBudget D (4 * B) (500000 * (D + 1) * (B + 1)^2) + 1 ≤
      600000 * (D + 1)^3 * (B + 1)^2 := by
  simp only [convolutionBudget, outerCost]
  ring_nf
  omega

/-- Polynomial parameter envelopes can be substituted directly into the
actual convolution budget; both growing dimensions remain explicit. -/
theorem convolutionBudget_parameter_le (D B A : ℕ)
    (hD : D + 1 ≤ A) (hB : B + 1 ≤ A^2) :
    convolutionBudget D (4 * B) (500000 * (D + 1) * (B + 1)^2) + 1 ≤
      600000 * A^7 := by
  apply (convolutionBudget_quartic_le D B).trans
  calc
    600000 * (D + 1)^3 * (B + 1)^2 ≤ 600000 * A^3 * (A^2)^2 := by gcongr
    _ = 600000 * A^7 := by ring

/-- The whole nested-loop command consumes the left input and row counter,
retains the right input and scalar frame, and writes the computed output. -/
theorem command_run (pair : Code) (base : Store) (encode : C → List Bool)
    (add mul : C → C → C) (D W pairCost : ℕ)
    (hpair : PairSpec pair base encode add mul D pairCost)
    (hencode : ∀ c, (encode c).length = W) (hwidth : (base 104).length = W)
    (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
    (w : Buffers) (P Q acc : List C) (hP : P.length = D) (hQ : Q.length = D)
    (hlen : acc.length = D) (hleft : w 0 = encodeArray encode P)
    (hright : w 1 = encodeArray encode Q) (hacc : w 2 = encodeArray encode acc)
    (hcount : (w 5).length = D) (h4 : w 4 = [])
    (h3 : w 3 = []) (h6 : w 6 = []) (h7 : w 7 = []) (h8 : w 8 = [])
    (h9 : w 9 = []) (h10 : w 10 = []) :
    ExecutesIn (command pair) (convolutionBudget D W pairCost) (buffers base w)
      (buffers base (finishedBuffers w
        (encodeArray encode (TruncatedConvolution.rows add mul Q 0 D P acc)))) := by
  let result := encodeArray encode (TruncatedConvolution.rows add mul Q 0 D P acc)
  let w' := outerDone w result D
  have hloop : ExecutesIn (outerLoop pair) (D * (outerCost D W pairCost + 2) + 2)
      (buffers base w) (buffers base w') := by
    have h := outerLoop_run pair base encode add mul D W pairCost hpair hencode hwidth
      h120 h121 h122 w P Q acc hQ hlen hleft hright hacc
      (hcount.trans hP.symm) (by simp [h4, hP]) h3 h6 h7 h8 h9 h10
    simpa [w', result, h4, hP] using h
  have hclear : ExecutesIn (clear 105) (2 * D + 3) (buffers base w')
      (buffers base (Function.update w' 4 [])) := by
    simpa [buffers_update, bufferPorts, w', outerDone, h4] using clear_run 105 (buffers base w')
  have hfinal : Function.update w' 4 [] = finishedBuffers w result := by
    funext j
    fin_cases j <;> simp [w', outerDone, finishedBuffers]
  have h := hloop.seq hclear
  rw [hfinal] at h
  change ExecutesIn (command pair) _ _ _ at h
  convert h using 1
  simp only [convolutionBudget]
  ring

/-- Specialization to an actual zero-initialized D-cell output array. -/
theorem initialized_command_run (pair : Code) (base : Store) (encode : C → List Bool)
    (zero : C) (add mul : C → C → C) (D W pairCost : ℕ)
    (hpair : PairSpec pair base encode add mul D pairCost)
    (hencode : ∀ c, (encode c).length = W) (hwidth : (base 104).length = W)
    (h120 : base 120 = []) (h121 : base 121 = []) (h122 : base 122 = [])
    (w : Buffers) (P Q : List C) (hP : P.length = D) (hQ : Q.length = D)
    (hleft : w 0 = encodeArray encode P) (hright : w 1 = encodeArray encode Q)
    (hacc : w 2 = encodeArray encode (List.replicate D zero))
    (hcount : (w 5).length = D) (h4 : w 4 = [])
    (h3 : w 3 = []) (h6 : w 6 = []) (h7 : w 7 = []) (h8 : w 8 = [])
    (h9 : w 9 = []) (h10 : w 10 = []) :
    ExecutesIn (command pair) (convolutionBudget D W pairCost) (buffers base w)
      (buffers base (finishedBuffers w
        (encodeArray encode (TruncatedConvolution.run zero add mul D P Q)))) :=
  command_run pair base encode add mul D W pairCost hpair hencode hwidth h120 h121 h122
    w P Q (List.replicate D zero) hP hQ (by simp) hleft hright hacc hcount h4 h3 h6 h7 h8 h9 h10

/-- The actual compiled finite table includes its final halt instruction. -/
theorem compiled_command_run (pair : Code) {budget : ℕ} {before after : Store}
    (h : ExecutesIn (command pair) budget before after) (regs : Fin 16 → Bool) :
    ∃ n regs', n ≤ budget + 1 ∧
      Trace (program pair) n
        ((⟨regs, before⟩ : Data).withPC (some (program pair).entry))
        ((⟨regs', after⟩ : Data).withPC none) := by
  obtain ⟨n, regs', hn, he⟩ := h regs
  exact ⟨n + 1, regs', Nat.add_le_add_right hn 1, compiled_halt_trace he 100 102⟩

/-- Primitive-machine execution is obtained from the verified compiler, with
its fixed per-program overhead displayed rather than treated as one step. -/
theorem primitive_command_run (pair : Code) {budget : ℕ} {before after : Store}
    (h : ExecutesIn (command pair) budget before after) (regs : Fin 16 → Bool) :
    ∃ n regs', n ≤ primitiveOverhead (program pair) * (budget + 1) ∧
      Computation.RunsIn (primitive (program pair)).step n
        (primitiveCfg (program pair) ((⟨regs, before⟩ : Data).withPC (some (program pair).entry)))
        (primitiveCfg (program pair) ((⟨regs', after⟩ : Data).withPC none)) := by
  obtain ⟨n, regs', hn, he⟩ := compiled_command_run pair h regs
  exact ⟨primitiveOverhead (program pair) * n, regs', Nat.mul_le_mul_left _ hn,
    primitive_trace _ he⟩

/-- Relocate the one fixed convolution program into a larger caller. -/
abbrev callAt {R S : ℕ} (pair : Code) (register : Fin 16 → Fin R)
    (stack : Fin 256 → Fin S) : Cmd R S :=
  liftCommand (command pair) 100 102 register stack

/-- The local run can be used from an arbitrary caller state. Its untouched
frame is retained by `embedState`; the subroutine return is charged. -/
theorem callAt_run {R S : ℕ} (pair : Code)
    (register : Fin 16 → Fin R) (stack : Fin 256 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    {budget : ℕ} {before after : Store}
    (h : ExecutesIn (command pair) budget before after)
    (d : State R S) (hbefore : d.stacks ∘ stack = before) :
    ∃ n regs', n ≤ budget + 1 ∧
      Eval (callAt pair register stack) n d
        (embedState register stack d (⟨regs', after⟩ : Data)) := by
  obtain ⟨n, regs', hn, he⟩ := h (d.regs ∘ register)
  have he' : Eval (command pair) n (projectState register stack d) (⟨regs', after⟩ : Data) := by
    simpa only [projectState, hbefore] using he
  exact ⟨n + 1, regs', Nat.add_le_add_right hn 1,
    eval_liftCommand_from_state (command pair) 100 102 register stack d hr hs he'⟩

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
