import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFlatCount

namespace OAI.Algorithms

/-! Runtime-degree readback of a reconstructed scalar count. The original
fixed program already reads a runtime B-bit first word and discards a suffix;
this theorem removes the old four-coordinate type restriction. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Readback

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpFlatCount

/-- Physical first-coordinate extraction, with arbitrary remaining dimension. -/
theorem extract_eval {B : ℕ} (hB : 0 < B)
    (word suffix : List Bool) (hword : word.length = B)
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B) :
    Eval extractCmd (14 * B + 2 * suffix.length + 16)
      (start regs modulus width (word ++ suffix))
      (finish (reset regs) modulus width word) := by
  let d₀ := start regs modulus width (word ++ suffix)
  let d₁ := peekState d₀
  let d₂ := SubexpScanPrimitives.afterTake d₁ 0 6 0 1 word suffix
  have hw : word ≠ [] := by intro h; simp [h] at hword; omega
  have hp : d₁.regs 1 = true := by
    cases he : word with
    | nil => exact False.elim (hw he)
    | cons b bs => simp [d₁, d₀, peekState, start, store, he]
  have ht := SubexpScanPrimitives.takeWord_eval d₁ 7 1 2 0 6 0 1
    (by decide) (by decide) word suffix
    (by simp [d₁, d₀, peekState, start, store])
    (by rfl) (by rfl) (by simp [d₁, d₀, peekState, start, store, hwidth, hword])
  have hc₀ := ListRegisterProgram.clear_run (0 : Fin 8) (0 : Fin 8) 1 d₂.regs d₂.stacks
  have hregs : reset d₂.regs = reset regs := by
    simp [reset, d₂, d₁, d₀, SubexpScanPrimitives.afterTake, peekState, start,
      StackRoutines.readRegs_reset]
  change readRegs d₂.regs 0 1 none = reset regs at hregs
  have hsource : d₂.stacks 0 = suffix := by simp [d₂, SubexpScanPrimitives.afterTake]
  have hstacks : StackRoutines.clearStacks 0 d₂.stacks = store [] modulus word width := by
    funext i
    fin_cases i <;> simp [d₂, d₁, d₀, SubexpScanPrimitives.afterTake, peekState,
      start, store, StackRoutines.clearStacks]
  have hc : Eval clearCmd (2 * suffix.length + 3) d₂
      (finish (reset regs) modulus width word) := by
    apply Eval.call
    simpa only [ListRegisterProgram.Run, hsource, hregs, hstacks, finish,
      StructuredProgram.State.withPC] using hc₀
  have ht' : Eval takeCmd (14 * B + 11) d₁ d₂ := by simpa only [takeCmd, hword] using ht
  have htotal : Eval extractCmd (1 + ((14 * B + 11 + (2 * suffix.length + 3)) + 1)) d₀
      (finish (reset regs) modulus width word) :=
    (peek_eval d₀).seq (Eval.ite_true (no := .base .skip) hp (ht'.seq hc))
  convert htotal using 1 ; omega

def extractProgram := compiled extractCmd 0 6

theorem extractProgram_run {B : ℕ} (hB : 0 < B)
    (word suffix : List Bool) (hword : word.length = B)
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B) :
    RunsIn extractProgram (14 * B + 2 * suffix.length + 17)
      ((start regs modulus width (word ++ suffix)).withPC (some extractProgram.entry))
      ((finish (reset regs) modulus width word).withPC none) := by
  refine ⟨14 * B + 2 * suffix.length + 16 + 1, by omega, ?_⟩
  exact compiled_halt_trace (extract_eval hB word suffix hword regs modulus width hwidth) 0 6

/-- The same dynamic-dimensional reader followed by the audited modular
positivity routine. The Boolean is physically written at output stack zero. -/
theorem decisionProgram_run {B : ℕ} (hB : 0 < B)
    (word suffix : List Bool) (hword : word.length = B)
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B) :
    ∃ finalRegs, RunsIn program (budget B modulus (word ++ suffix))
      ((start regs modulus width (word ++ suffix)).withPC (some program.entry))
      (⟨none, finalRegs, store (output modulus word) modulus [] width⟩ : Cfg 8 8 _) := by
  have he := extract_eval hB word suffix hword regs modulus width hwidth
  obtain ⟨steps, finalRegs, hs, hd⟩ := decode_eval (reset regs) modulus width word
  refine ⟨finalRegs, 14 * B + 2 * suffix.length + 16 + steps + 1, ?_,
    compiled_halt_trace (he.seq hd) 0 0⟩
  dsimp [budget]
  simp only [List.length_append, hword] at *
  omega

end SubexponentialSAT.SqrtLog.LeafProgram.Readback

end OAI.Algorithms
