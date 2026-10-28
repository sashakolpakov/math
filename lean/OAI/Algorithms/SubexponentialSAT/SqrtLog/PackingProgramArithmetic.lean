import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls

namespace OAI.Algorithms

/-! One fixed binary machine combines the two collision counts. Its instruction
count and every output length are charged in terms of actual input bit lengths. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

abbrev ArithmeticData := SubexponentialSAT.StructuredProgram.State 8 12

def arithmeticWork : Fin 5 ↪ Fin 12 where
  toFun i := ⟨i.val + 7, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

def firstProductPorts : Ports 12 where
  left := 0
  right := 1
  out := 4
  work := arithmeticWork
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

def secondProductPorts : Ports 12 where
  left := 2
  right := 3
  out := 5
  work := arithmeticWork
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

def productSumPorts : Ports 12 where
  left := 4
  right := 5
  out := 6
  work := arithmeticWork
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

abbrev weightedScoreCommand : Cmd 8 12 :=
  .seq (multiplyAt firstProductPorts)
    (.seq (multiplyAt secondProductPorts) (addAt productSumPorts))

abbrev weightedScoreProgram := compiled weightedScoreCommand 0 6

def arithmeticInputLength (d : ArithmeticData) : ℕ :=
  (d.stacks 0).length + (d.stacks 1).length +
    (d.stacks 2).length + (d.stacks 3).length

def weightedScoreValue (d : ArithmeticData) : ℕ :=
  SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 0) * SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 1) +
    SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 2) * SubexponentialSAT.BinaryArithmetic.toNat (d.stacks 3)

def arithmeticReady (d : ArithmeticData) : Prop :=
  ∀ j : Fin 12, 4 ≤ j.val → d.stacks j = []

/-- Intermediate product ports 4 and 5 and output port 6 are written; source
ports and five scratch ports are preserved. The bound is quadratic in bits. -/
theorem weightedScoreCommand_eval (d : ArithmeticData) (hd : arithmeticReady d) :
    ∃ t ≤ 300 * (arithmeticInputLength d + 3)^2, ∃ e : ArithmeticData,
      Eval weightedScoreCommand t d e ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks 6) = weightedScoreValue d ∧
      (e.stacks 6).length ≤ arithmeticInputLength d + 3 ∧
      (∀ j : Fin 12, j ≠ 4 → j ≠ 5 → j ≠ 6 → e.stacks j = d.stacks j) := by
  have hv1 : Valid firstProductPorts d := by
    constructor
    · exact hd 4 (by decide)
    · intro i; exact hd (arithmeticWork i) (by fin_cases i <;> decide)
  obtain ⟨t₁, r₁, p₁, hrun₁, hvalue₁, hlen₁, ht₁⟩ := multiplyAt_eval firstProductPorts d hv1
  let d₁ : ArithmeticData := ⟨r₁, Function.update d.stacks 4 p₁⟩
  have hv2 : Valid secondProductPorts d₁ := by
    constructor
    · simpa [d₁, secondProductPorts] using hd 5 (by decide)
    · intro i
      have hi : arithmeticWork i ≠ 4 := by fin_cases i <;> decide
      simp only [d₁, secondProductPorts ]
      exact hd (arithmeticWork i) (by fin_cases i <;> decide)
  obtain ⟨t₂, r₂, p₂, hrun₂, hvalue₂, hlen₂, ht₂⟩ := multiplyAt_eval secondProductPorts d₁ hv2
  let d₂ : ArithmeticData := ⟨r₂, Function.update d₁.stacks 5 p₂⟩
  have hv3 : Valid productSumPorts d₂ := by
    constructor
    · simpa [d₂, d₁, productSumPorts] using hd 6 (by decide)
    · intro i
      have hi4 : arithmeticWork i ≠ 4 := by fin_cases i <;> decide
      have hi5 : arithmeticWork i ≠ 5 := by fin_cases i <;> decide
      simp only [d₂, d₁, productSumPorts  ]
      exact hd (arithmeticWork i) (by fin_cases i <;> decide)
  obtain ⟨t₃, r₃, out, hrun₃, hvalue₃, hlen₃, ht₃⟩ := addAt_eval productSumPorts d₂ hv3
  let e : ArithmeticData := ⟨r₃, Function.update d₂.stacks 6 out⟩
  have hvals : SubexponentialSAT.BinaryArithmetic.toNat out = weightedScoreValue d := by
    simp only [firstProductPorts] at hvalue₁
    simp [d₁, secondProductPorts] at hvalue₂
    simp [d₂, d₁, productSumPorts] at hvalue₃
    simpa [weightedScoreValue, hvalue₁, hvalue₂] using hvalue₃
  have hl1 : p₁.length ≤ (d.stacks 0).length + (d.stacks 1).length + 1 := hlen₁
  have hl2 : p₂.length ≤ (d.stacks 2).length + (d.stacks 3).length + 1 := by
    simpa [d₁, secondProductPorts] using hlen₂
  have hl3 : out.length ≤ p₁.length + p₂.length + 1 := by
    simpa [d₂, d₁, productSumPorts] using hlen₃
  have hb1 : (d.stacks firstProductPorts.left).length +
      (d.stacks firstProductPorts.right).length + 1 ≤ arithmeticInputLength d + 3 := by
    dsimp [firstProductPorts, arithmeticInputLength]
    omega
  have hb2 : (d₁.stacks secondProductPorts.left).length +
      (d₁.stacks secondProductPorts.right).length + 1 ≤ arithmeticInputLength d + 3 := by
    simp [d₁, secondProductPorts, arithmeticInputLength]
    omega
  have hb3 : (d₂.stacks productSumPorts.left).length +
      (d₂.stacks productSumPorts.right).length + 1 ≤ arithmeticInputLength d + 3 := by
    change p₁.length + p₂.length + 1 ≤ arithmeticInputLength d + 3
    dsimp [arithmeticInputLength]
    omega
  have ht1 : t₁ ≤ 100 * (arithmeticInputLength d + 3)^2 :=
    ht₁.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb1 _))
  have ht2 : t₂ ≤ 100 * (arithmeticInputLength d + 3)^2 :=
    ht₂.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb2 _))
  have ht3 : t₃ ≤ 100 * (arithmeticInputLength d + 3)^2 :=
    ht₃.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb3 _))
  refine ⟨t₁+(t₂+t₃), by omega, e, ?_, ?_, ?_, ?_⟩
  · exact hrun₁.seq (hrun₂.seq hrun₃)
  · simpa [e] using hvals
  · simpa [e, arithmeticInputLength] using (show out.length ≤ arithmeticInputLength d + 3 by
      dsimp [arithmeticInputLength]; omega)
  · intro j hj4 hj5 hj6
    simp [e, d₂, d₁, hj4, hj5, hj6]

/-- The same single finite instruction table terminates on all valid inputs. -/
theorem weightedScoreProgram_runsIn (d : ArithmeticData) (hd : arithmeticReady d) :
    ∃ e : ArithmeticData,
      RunsIn weightedScoreProgram (300*(arithmeticInputLength d+3)^2+1)
        (d.withPC (some weightedScoreProgram.entry)) (e.withPC none) ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks 6) = weightedScoreValue d := by
  obtain ⟨t, ht, e, he, hv, hl, hf⟩ := weightedScoreCommand_eval d hd
  exact ⟨e, ⟨t+1, by omega, compiled_halt_trace he 0 6⟩, hv⟩

theorem weightedScoreProgram_primitive (d : ArithmeticData) (hd : arithmeticReady d) :
    ∃ e : ArithmeticData,
      SubexponentialSAT.Computation.RunsIn (primitive weightedScoreProgram).step
        (primitiveOverhead weightedScoreProgram * (300*(arithmeticInputLength d+3)^2+1))
        (primitiveCfg weightedScoreProgram (d.withPC (some weightedScoreProgram.entry)))
        (primitiveCfg weightedScoreProgram (e.withPC none)) ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks 6) = weightedScoreValue d := by
  obtain ⟨e, he, hv⟩ := weightedScoreProgram_runsIn d hd
  exact ⟨e, primitive_execution weightedScoreProgram he, hv⟩
end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
