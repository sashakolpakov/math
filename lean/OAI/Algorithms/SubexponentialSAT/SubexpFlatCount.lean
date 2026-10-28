import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDecodeProgram
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# Count decisions from the actual flat coefficient representation

Coefficients are stored constant-first, with four consecutive little-endian
words per coefficient. Width and modulus are runtime data. This adapter reads
the first word, discards the unused polynomial suffix, and executes the checked
remainder-and-positivity program. It does not serialize the array into records.
-/

namespace SubexponentialSAT.SubexpFlatCount

open BitProgram StructuredCalls ProgramLinking

abbrev Code (B : ℕ) := SubexpQuarticRing.Quad (SubexpQuarticRing.Word B)

def firstWord {B : ℕ} : List (Code B) → List Bool
  | [] => []
  | a :: _ => a.c0.val

theorem firstWord_length_le {B : ℕ} (P : List (Code B)) :
    (firstWord P).length ≤ B := by
  cases P with
  | nil => exact Nat.zero_le B
  | cons a _ => exact a.c0.property.le

abbrev Data := State 8 8

def flatCoefficient {B : ℕ} (a : Code B) : List Bool :=
  a.c0.val ++ (a.c1.val ++ (a.c2.val ++ a.c3.val))

def flatPolynomial {B : ℕ} (P : List (Code B)) : List Bool :=
  P.flatMap flatCoefficient

def suffix {B : ℕ} (a : Code B) (P : List (Code B)) : List Bool :=
  a.c1.val ++ (a.c2.val ++ (a.c3.val ++ flatPolynomial P))

theorem flatPolynomial_cons {B : ℕ} (a : Code B) (P : List (Code B)) :
    flatPolynomial (a :: P) = a.c0.val ++ suffix a P := by
  simp [flatPolynomial, flatCoefficient, suffix, List.append_assoc]

theorem flatPolynomial_length {B : ℕ} (P : List (Code B)) :
    (flatPolynomial P).length = 4 * B * P.length := by
  induction P with
  | nil => simp [flatPolynomial]
  | cons a P ih =>
      simp only [flatPolynomial, List.flatMap_cons, List.length_append] at *
      simp [flatCoefficient, a.c0.property, a.c1.property, a.c2.property,
        a.c3.property, ih, Nat.mul_add ]
      omega

/-- The producer's word-list flattening is this same bit stream. -/
theorem flatPolynomial_eq_words {B : ℕ} (P : List (Code B)) :
    flatPolynomial P =
      ((P.flatMap (fun a => [a.c0, a.c1, a.c2, a.c3])).map Subtype.val).flatten := by
  induction P with
  | nil => rfl
  | cons a P ih => simp [flatPolynomial, flatCoefficient, List.append_assoc] at *; exact ih

def store (input modulus word width : List Bool) : Fin 8 → List Bool :=
  ![input, [], [], [], [], modulus, word, width]

def start (regs : Fin 8 → Bool) (modulus width input : List Bool) : Data :=
  ⟨regs, store input modulus [] width⟩

def finish (regs : Fin 8 → Bool) (modulus width word : List Bool) : Data :=
  ⟨regs, store [] modulus word width⟩

def reset (regs : Fin 8 → Bool) : Fin 8 → Bool := readRegs regs 0 1 none

def peekState (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 (d.stacks 0).head?, d.stacks⟩

abbrev peekCmd : Cmd 8 8 := .base (.atom (.peek 0 0 1))

theorem peek_eval (d : Data) : Eval peekCmd 1 d (peekState d) :=
  .base (.atom _ _)

abbrev takeCmd : Cmd 8 8 := SubexpScanPrimitives.takeWord 7 1 2 0 6 0 1
abbrev clearCmd : Cmd 8 8 := .call (StackRoutines.clearProgram 0 0 1)

abbrev extractCmd : Cmd 8 8 :=
  .seq peekCmd (.ite 1 (.seq takeCmd clearCmd) (.base .skip))

def extractCost {B : ℕ} : List (Code B) → ℕ
  | [] => 2
  | a :: P => 14 * B + 2 * (suffix a P).length + 16

theorem extract_eval {B : ℕ} (hB : 0 < B) (P : List (Code B))
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B) :
    Eval extractCmd (extractCost P) (start regs modulus width (flatPolynomial P))
      (finish (reset regs) modulus width (firstWord P)) := by
  cases P with
  | nil =>
      have hp := peek_eval (start regs modulus width [])
      have he : peekState (start regs modulus width []) = finish (reset regs) modulus width [] := rfl
      rw [he] at hp
      have hf : (finish (reset regs) modulus width []).regs 1 = false := by simp [finish, reset]
      exact hp.seq (.ite_false hf (.base (.skip _)))
  | cons a P =>
      let d₀ := start regs modulus width (flatPolynomial (a :: P))
      let d₁ := peekState d₀
      let d₂ := SubexpScanPrimitives.afterTake d₁ 0 6 0 1 a.c0.val (suffix a P)
      have ha : a.c0.val ≠ [] := by
        intro he
        have := a.c0.property
        simp [he] at this
        omega
      have hp : d₁.regs 1 = true := by
        cases he : a.c0.val with
        | nil => exact False.elim (ha he)
        | cons b bs => simp [d₁, d₀, peekState, start, store, flatPolynomial_cons, he]
      have ht := SubexpScanPrimitives.takeWord_eval d₁ 7 1 2 0 6 0 1
        (by decide) (by decide) a.c0.val (suffix a P)
        (by simp [d₁, d₀, peekState, start, store, flatPolynomial_cons])
        (by rfl) (by rfl) (by simp [d₁, d₀, peekState, start, store, hwidth, a.c0.property])
      have hc₀ := ListRegisterProgram.clear_run (0 : Fin 8) (0 : Fin 8) 1
        d₂.regs d₂.stacks
      have hregs : reset d₂.regs = reset regs := by
        simp [reset, d₂, d₁, d₀, SubexpScanPrimitives.afterTake, peekState, start,
          StackRoutines.readRegs_reset]
      change readRegs d₂.regs 0 1 none = reset regs at hregs
      have hsource : d₂.stacks 0 = suffix a P := by
        simp [d₂, SubexpScanPrimitives.afterTake]
      have hstacks : StackRoutines.clearStacks 0 d₂.stacks =
          store [] modulus a.c0.val width := by
        funext i
        fin_cases i <;> simp [d₂, d₁, d₀, SubexpScanPrimitives.afterTake, peekState,
          start, store, StackRoutines.clearStacks]
      have hc : Eval clearCmd (2 * (suffix a P).length + 3) d₂
          (finish (reset regs) modulus width a.c0.val) := by
        apply Eval.call
        simpa only [ListRegisterProgram.Run, hsource, hregs, hstacks,
          finish, StructuredProgram.State.withPC] using hc₀
      have ht' : Eval takeCmd (14 * B + 11) d₁ d₂ := by
        simpa only [takeCmd, a.c0.property] using ht
      have htotal : Eval extractCmd
          (1 + ((14 * B + 11 + (2 * (suffix a P).length + 3)) + 1)) d₀
          (finish (reset regs) modulus width a.c0.val) :=
        (peek_eval d₀).seq (Eval.ite_true (no := .base .skip) hp (ht'.seq hc))
      have hcost : 1 + ((14 * B + 11 + (2 * (suffix a P).length + 3)) + 1) =
          extractCost (a :: P) := by
        simp only [extractCost]
        omega
      rw [hcost] at htotal
      exact htotal

theorem extractCost_le {B : ℕ} (P : List (Code B)) :
    extractCost P ≤ 16 * ((flatPolynomial P).length + B + 1) := by
  cases P with
  | nil => simp [extractCost, flatPolynomial]; omega
  | cons a P =>
      rw [extractCost, flatPolynomial_cons, List.length_append, a.c0.property]
      omega

def decoderPorts : Fin 7 → Fin 8 := Fin.castSucc

theorem decoderPorts_injective : Function.Injective decoderPorts := Fin.castSucc_injective 7

abbrev decodeProgram : Program 8 8 96 :=
  liftProgram SubexpDecodeProgram.program id decoderPorts

private theorem embed_decode (pc : Option (Fin 96)) (regs frameRegs : Fin 8 → Bool)
    (input modulus word width : List Bool) :
    embedCfg id decoderPorts id none
      (⟨none, frameRegs, store [] modulus [] width⟩ : Cfg 8 8 96)
      ⟨pc, regs, ModularDivisionPrograms.resting input modulus word⟩ =
      ⟨pc, regs, store input modulus word width⟩ := by
  apply embedCfg_eq_of_ports id decoderPorts id none _ _ _
    Function.injective_id decoderPorts_injective
  · cases pc <;> rfl
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨2, rfl⟩)
    · exact False.elim (hi ⟨3, rfl⟩)
    · exact False.elim (hi ⟨4, rfl⟩)
    · exact False.elim (hi ⟨5, rfl⟩)
    · exact False.elim (hi ⟨6, rfl⟩)
    · rfl

def output (modulus word : List Bool) : List Bool :=
  SubexpDecodeProgram.answer modulus word ::
    PositiveWordProgram.residual (ModularArithmetic.reduce modulus word)

theorem decode_eval (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    ∃ steps finalRegs, steps ≤ 105 * (modulus.length + word.length + 1)^2 ∧
      Eval (.call decodeProgram) steps (finish regs modulus width word)
        ⟨finalRegs, store (output modulus word) modulus [] width⟩ := by
  obtain ⟨finalRegs, steps, hsteps, ht⟩ := SubexpDecodeProgram.run regs modulus word
  have h := liftProgram_trace SubexpDecodeProgram.program id decoderPorts
    (⟨none, regs, store [] modulus [] width⟩ : Cfg 8 8 96)
    Function.injective_id decoderPorts_injective ht
  rw [embed_decode, embed_decode] at h
  refine ⟨steps, finalRegs, hsteps, .call _ ?_⟩
  exact h

abbrev command : Cmd 8 8 := .seq extractCmd (.call decodeProgram)

abbrev program : Program 8 8 (size command + 1) := compiled command 0 0

def budget (B : ℕ) (modulus input : List Bool) : ℕ :=
  16 * (input.length + B + 1) + 105 * (modulus.length + B + 1)^2 + 1

theorem run {B : ℕ} (hB : 0 < B) (P : List (Code B))
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B) :
    ∃ finalRegs,
      RunsIn program (budget B modulus (flatPolynomial P))
        ((start regs modulus width (flatPolynomial P)).withPC (some program.entry))
        ⟨none, finalRegs, store (output modulus (firstWord P)) modulus [] width⟩ := by
  have he := extract_eval hB P regs modulus width hwidth
  obtain ⟨steps, finalRegs, hb, hd⟩ := decode_eval (reset regs) modulus width (firstWord P)
  have ht := compiled_halt_trace (he.seq hd) 0 0
  refine ⟨finalRegs, extractCost P + steps + 1, ?_, ht⟩
  have hw := firstWord_length_le P
  have hd' : 105 * (modulus.length + (firstWord P).length + 1)^2 ≤
      105 * (modulus.length + B + 1)^2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have hx := extractCost_le P
  dsimp [budget]
  omega

theorem primitive_run {B : ℕ} (hB : 0 < B) (P : List (Code B))
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B) :
    ∃ finalRegs,
      Computation.RunsIn (primitive program).step
        (primitiveOverhead program * budget B modulus (flatPolynomial P))
        (primitiveCfg program
          ((start regs modulus width (flatPolynomial P)).withPC (some program.entry)))
        (primitiveCfg program
          ⟨none, finalRegs, store (output modulus (firstWord P)) modulus [] width⟩) := by
  obtain ⟨finalRegs, hr⟩ := run hB P regs modulus width hwidth
  exact ⟨finalRegs, primitive_execution program hr⟩

end SubexponentialSAT.SubexpFlatCount

end OAI.Algorithms
