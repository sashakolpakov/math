import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpConvolutionStore

namespace OAI.Algorithms

/-! Preserve a local-factor array and extract its constant coefficient for
the scalar inverse. The array is constant first on 240, its coefficient
width is on 104, and the copied constant cell is returned on 248. -/

namespace SubexponentialSAT.SubexpLocalConstantProgram

open BitProgram StructuredCalls SubexpConvolutionControl

def command : Code := .seq (copy 240 247) (.seq (takeCell 247 248) (clear 247))
def program := compiled command 240 248

/-- For the selected lift exponent μ=D+1, construct the D+μ geometric-loop
counter by two actual copies of D and one pushed token. -/
def seriesCounter : Code :=
  .seq (copy 243 246) (.seq (copy 243 246)
    (.seq (.base (.atom (.set 0 true))) (.base (.atom (.push 246 0)))))

theorem seriesCounter_run (s : Store) (D : ℕ)
    (hD : s 243 = List.replicate D true) (h246 : s 246 = []) (h120 : s 120 = []) :
    ExecutesIn seriesCounter (14 * D + 12) s
      (Function.update s 246 (List.replicate (D + (D + 1)) true)) := by
  let s₁ := Function.update s 246 (List.replicate D true)
  let s₂ := Function.update s 246 (List.replicate (D + D) true)
  have h₁ : ExecutesIn (copy 243 246) (7 * D + 5) s s₁ := by
    simpa [s₁, hD, h246] using copy_run 243 246 s
      (by decide) (by decide) (by decide) h120
  have h₂ : ExecutesIn (copy 243 246) (7 * D + 5) s₁ s₂ := by
    have hs243 : s₁ 243 = List.replicate D true := by simp [s₁, hD]
    have hs246 : s₁ 246 = List.replicate D true := by simp [s₁]
    have he : Function.update s₁ 246 (s₁ 243 ++ s₁ 246) = s₂ := by
      rw [hs243, hs246, ← List.replicate_add]
      simp [s₁, s₂]
    have h := copy_run 243 246 s₁ (by decide) (by decide) (by decide)
      (by simp [s₁, h120])
    rw [he, hs243, List.length_replicate] at h
    exact h
  have h₃ : ExecutesIn
      (.seq (.base (.atom (.set 0 true))) (.base (.atom (.push 246 0)))) 2 s₂
      (Function.update s 246 (List.replicate (D + (D + 1)) true)) := by
    intro regs
    let d : Data := ⟨regs, s₂⟩
    have hs := Eval.base (StructuredProgram.Eval.atom (.set 0 true) d)
    have hp := Eval.base (StructuredProgram.Eval.atom (.push 246 0)
      ((StructuredProgram.Atom.set 0 true).eval d))
    refine ⟨2, Function.update regs 0 true, le_rfl, ?_⟩
    convert hs.seq hp using 1
    apply SubexpScanPrimitives.state_ext
    · rfl
    · simp [d, s₂, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr,
        List.replicate_succ, ← Nat.add_assoc]
  have h := h₁.seq (h₂.seq h₃)
  convert h using 1
  all_goals first | rfl | ring

theorem command_run (s : Store) (constant rest : List Bool)
    (harray : s 240 = constant ++ rest)
    (hwidth : (s 104).length = constant.length)
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h247 : s 247 = []) (h248 : s 248 = []) :
    ExecutesIn command (21 * constant.length + 9 * rest.length + 19)
      s (Function.update s 248 constant) := by
  let s₁ := Function.update s 247 (constant ++ rest)
  let s₂ := Function.update (Function.update s 247 rest) 248 constant
  have h₁ : ExecutesIn (copy 240 247)
      (7 * (constant.length + rest.length) + 5) s s₁ := by
    simpa [s₁, harray, h247] using copy_run 240 247 s
      (by decide) (by decide) (by decide) h120
  have h₂ : ExecutesIn (takeCell 247 248) (14 * constant.length + 11) s₁ s₂ := by
    simpa [s₁, s₂, h248] using takeCell_run 247 248 s₁ constant rest
      (by decide) (by simp [s₁]) (by simp [s₁, h121]) (by simp [s₁, h122])
      (by simpa [s₁] using hwidth)
  have he : Function.update s₂ 247 [] = Function.update s 248 constant := by
    funext i
    by_cases hi : i = 247 <;> simp [s₂, hi, h247, Function.update_apply]
  have h₃ : ExecutesIn (clear 247) (2 * rest.length + 3) s₂
      (Function.update s 248 constant) := by
    have h := clear_run 247 s₂
    rw [he] at h
    simpa [s₂] using h
  have h := h₁.seq (h₂.seq h₃)
  convert h using 1
  all_goals first | rfl | ring

theorem program_run (s : Store) (constant rest : List Bool)
    (harray : s 240 = constant ++ rest)
    (hwidth : (s 104).length = constant.length)
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h247 : s 247 = []) (h248 : s 248 = []) (regs : Fin 16 → Bool) :
    ∃ n regs', n ≤ 21 * constant.length + 9 * rest.length + 20 ∧
      Trace program n ((⟨regs, s⟩ : Data).withPC (some program.entry))
        ((⟨regs', Function.update s 248 constant⟩ : Data).withPC none) := by
  obtain ⟨n, regs', hn, he⟩ := command_run s constant rest harray hwidth
    h120 h121 h122 h247 h248 regs
  exact ⟨n + 1, regs', by omega, compiled_halt_trace he 240 248⟩

theorem primitive_run (s : Store) (constant rest : List Bool)
    (harray : s 240 = constant ++ rest)
    (hwidth : (s 104).length = constant.length)
    (h120 : s 120 = []) (h121 : s 121 = []) (h122 : s 122 = [])
    (h247 : s 247 = []) (h248 : s 248 = []) (regs : Fin 16 → Bool) :
    ∃ n regs', n ≤ primitiveOverhead program *
        (21 * constant.length + 9 * rest.length + 20) ∧
      Computation.RunsIn (primitive program).step n
        (primitiveCfg program ((⟨regs, s⟩ : Data).withPC (some program.entry)))
        (primitiveCfg program ((⟨regs', Function.update s 248 constant⟩ : Data).withPC none)) := by
  obtain ⟨n, regs', hn, he⟩ := program_run s constant rest harray hwidth
    h120 h121 h122 h247 h248 regs
  exact ⟨primitiveOverhead program * n, regs', Nat.mul_le_mul_left _ hn, primitive_trace _ he⟩

end SubexponentialSAT.SubexpLocalConstantProgram

end OAI.Algorithms
