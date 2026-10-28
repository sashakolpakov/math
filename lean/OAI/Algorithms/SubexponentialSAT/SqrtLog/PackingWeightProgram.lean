import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingWeightProgramBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.PackingWeightProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

/-- The two output words are binary; the initial sources and every other stack
are preserved. Arithmetic is valid even when an input denotes zero. -/
theorem command_eval (d : Data) (hd : ready d) :
    ∃ t ≤ 500 * (2 * inputLength d + 4)^2, ∃ e : Data,
      Eval command t d e ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks 4) = incidence d ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks 5) = head d ∧
      (e.stacks 4).length ≤ 2 * (d.stacks 0).length + 2 * (d.stacks 1).length + 3 ∧
      (e.stacks 5).length ≤ 2 * (d.stacks 2).length + 2 * (d.stacks 3).length + 6 ∧
      (∀ j, j ≠ 4 → j ≠ 5 → e.stacks j = d.stacks j) := by
  have hv0 : Valid (ports 0) d := by
    constructor
    · exact hd 6 (by decide)
    · intro i; exact hd (work i) (by fin_cases i <;> decide)
  obtain ⟨t₀, r₀, w₀, he₀, hv₀, hl₀, ht₀⟩ := multiplyAt_eval (ports 0) d hv0
  let d₁ : Data := ⟨r₀, Function.update d.stacks 6 w₀⟩
  have hv1 : Valid (ports 1) d₁ := by
    constructor
    · simpa [d₁, ports] using hd 4 (by decide)
    · intro i
      have hi : work i ≠ 6 := (ports 0).work_ne_out i
      simpa [d₁, ports, hi] using hv0.2 i
  obtain ⟨t₁, r₁, w₁, he₁, hv₁, hl₁, ht₁⟩ := multiplyAt_eval (ports 1) d₁ hv1
  let d₂ : Data := ⟨r₁, Function.update d₁.stacks 4 w₁⟩
  have hv2 : Valid (ports 2) d₂ := by
    constructor
    · simpa [d₂, d₁, ports] using hd 7 (by decide)
    · intro i
      have hi : work i ≠ 4 := (ports 1).work_ne_out i
      simpa [d₂, ports, hi] using hv1.2 i
  obtain ⟨t₂, r₂, w₂, he₂, hv₂, hl₂, ht₂⟩ := multiplyAt_eval (ports 2) d₂ hv2
  let d₃ : Data := ⟨r₂, Function.update d₂.stacks 7 w₂⟩
  have hv3 : Valid (ports 3) d₃ := by
    constructor
    · simpa [d₃, d₂, d₁, ports] using hd 5 (by decide)
    · intro i
      have hi : work i ≠ 7 := (ports 2).work_ne_out i
      simpa [d₃, ports, hi] using hv2.2 i
  obtain ⟨t₃, r₃, w₃, he₃, hv₃, hl₃, ht₃⟩ := multiplyAt_eval (ports 3) d₃ hv3
  let d₄ : Data := ⟨r₃, Function.update d₃.stacks 5 w₃⟩
  let d₅ := shifted d₄
  let d₆ := cleared d₅ 6
  let e := cleared d₆ 7
  have hs := shift_eval d₄
  have hc6 := clear_eval d₅ 6
  have hc7 := clear_eval d₆ 7
  have hl0 : w₀.length ≤ (d.stacks 0).length + (d.stacks 1).length + 1 := hl₀
  have hl1 : w₁.length ≤ 2 * w₀.length + 1 := by simpa [d₁, ports, two_mul] using hl₁
  have hl2 : w₂.length ≤ (d.stacks 2).length + (d.stacks 3).length + 1 := by
    simpa [d₂, d₁, ports] using hl₂
  have hl3 : w₃.length ≤ 2 * w₂.length + 1 := by simpa [d₃, ports, two_mul] using hl₃
  have htime0 : t₀ ≤ 100 * (2 * inputLength d + 4)^2 := by
    apply ht₀.trans; apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left
    dsimp [ports, inputLength]; omega
  have htime1 : t₁ ≤ 100 * (2 * inputLength d + 4)^2 := by
    apply ht₁.trans; apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left
    simp only [ports, Matrix.cons_val_one, Matrix.cons_val_zero, d₁,
      Function.update_self]
    dsimp [inputLength]; omega
  have htime2 : t₂ ≤ 100 * (2 * inputLength d + 4)^2 := by
    apply ht₂.trans; apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left
    simp [ports, d₂, d₁, inputLength]; omega
  have htime3 : t₃ ≤ 100 * (2 * inputLength d + 4)^2 := by
    apply ht₃.trans; apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left
    simp [ports, d₃, inputLength]; omega
  have hlen6 : (d₅.stacks 6).length = w₀.length := by
    simp [d₅, shifted, d₄, d₃, d₂, d₁]
  have hlen7 : (d₆.stacks 7).length = w₂.length := by
    simp [d₆, cleared, d₅, shifted, d₄, d₃]
  refine ⟨t₀ + (t₁ + (t₂ + (t₃ + (6 +
    ((2 * (d₅.stacks 6).length + 3) + (2 * (d₆.stacks 7).length + 3)))))),
    ?_, e, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hlen6, hlen7]
    have hsum : w₀.length + w₂.length ≤ inputLength d + 2 := by
      dsimp [inputLength]; omega
    nlinarith only [hsum, htime0, htime1, htime2, htime3]
  · exact he₀.seq (he₁.seq (he₂.seq (he₃.seq (hs.seq (hc6.seq hc7)))))
  · simp [e, d₆, cleared, d₅, shifted, d₄, d₃, d₂]
    simp [ports] at hv₀
    simp [ports, d₁] at hv₁
    rw [hv₁, hv₀]
    dsimp [incidence]
    ring
  · simp [e, d₆, cleared, d₅, shifted, d₄]
    simp [ports, d₂, d₁] at hv₂
    simp [ports, d₃] at hv₃
    rw [hv₃, hv₂]
    dsimp [head]
    ring
  · simp [e, d₆, cleared, d₅, shifted, d₄, d₃, d₂]
    omega
  · simp [e, d₆, cleared, d₅, shifted, d₄]
    omega
  · intro j hj4 hj5
    by_cases hj6 : j = 6
    · subst j; simp [e, d₆, cleared, hd 6 (by decide)]
    by_cases hj7 : j = 7
    · subst j; simp [e, cleared, hd 7 (by decide)]
    simp [e, d₆, cleared, d₅, shifted, d₄, d₃, d₂, d₁, hj4, hj5, hj6, hj7]

end SubexponentialSAT.SqrtLog.PackingWeightProgram

end OAI.Algorithms
