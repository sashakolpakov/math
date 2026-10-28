import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudget
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.ParameterBank
import OAI.Algorithms.SubexponentialSAT.ModularArithmetic
import OAI.Algorithms.SubexponentialSAT.BitProgramSpace

/-!
Concrete finite-control construction of the Appendix A dyadic search.
The input budget is `1 / s`; the search uses only exact binary arithmetic.
This file separates command construction from theorems about its execution.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram

open BitProgram StructuredCalls BinaryArithmetic
open ParametersProgram
open scoped BigOperators

@[simp] theorem bits_three_length : (3 : ℕ).bits.length = 2 := by
  rw [Nat.bit1_bits 1, Nat.one_bits]
  rfl

@[simp] theorem bits_four_length : (4 : ℕ).bits.length = 3 := by
  rw [Nat.bit0_bits 2 (by decide), Nat.bit0_bits 1 (by decide), Nat.one_bits]
  rfl

@[simp] theorem bits_sixteen_length : (16 : ℕ).bits.length = 5 := by
  rw [Nat.bit0_bits 8 (by decide), Nat.bit0_bits 4 (by decide),
    Nat.bit0_bits 2 (by decide), Nat.bit0_bits 1 (by decide), Nat.one_bits]
  rfl

inductive Arithmetic where
  | add
  | multiply

def Arithmetic.value : Arithmetic → ℕ → ℕ → ℕ
  | .add => (· + ·)
  | .multiply => (· * ·)

def Arithmetic.command (op : Arithmetic) (a b o : Fin 19)
    (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 32 :=
  match op with
  | .add => addCmd a b o hoa hob
  | .multiply => multiplyCmd a b o hoa hob

theorem Arithmetic.eval (op : Arithmetic) (r : Regs) (w : Words)
    (a b o : Fin 19) (hoa : o ≠ a) (hob : o ≠ b) (ho : w o = []) :
    ∃ t rf word, Eval (op.command a b o hoa hob) t (state r w)
        (state rf (Function.update w o word)) ∧
      toNat word = op.value (toNat (w a)) (toNat (w b)) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 100 * ((w a).length + (w b).length + 1) ^ 2 := by
  cases op with
  | add => exact add_eval r w a b o hoa hob ho
  | multiply => exact multiply_eval r w a b o hoa hob ho

/-- The temporary is emptied before returning; the destination may be an operand. -/
def replaceCmd (op : Arithmetic) (a b o tmp : Fin 19)
    (hta : tmp ≠ a) (htb : tmp ≠ b) : Cmd 8 32 :=
  .seq (op.command a b tmp hta htb)
    (.seq (clearCmd o) (.seq (copyCmd tmp o) (clearCmd tmp)))

theorem replace_eval (op : Arithmetic) (r : Regs) (w : Words)
    (a b o tmp : Fin 19) (hta : tmp ≠ a) (htb : tmp ≠ b)
    (hto : tmp ≠ o) (ht : w tmp = []) :
    ∃ t rf word, Eval (replaceCmd op a b o tmp hta htb) t (state r w)
        (state rf (Function.update w o word)) ∧
      toNat word = op.value (toNat (w a)) (toNat (w b)) ∧
      word.length ≤ (w a).length + (w b).length + 1 ∧
      t ≤ 150 * ((w a).length + (w b).length + (w o).length + 2) ^ 2 := by
  obtain ⟨t, r₁, word, he, hv, hl, htime⟩ := op.eval r w a b tmp hta htb ht
  obtain ⟨r₂, hc⟩ := clear_eval r₁ (Function.update w tmp word) o
  obtain ⟨r₃, hp⟩ := copy_eval r₂ (Function.update (Function.update w tmp word) o [])
    tmp o hto.symm (by simp)
  obtain ⟨r₄, hz⟩ := clear_eval r₃
    (Function.update (Function.update (Function.update w tmp word) o []) o word) tmp
  have hframe : Function.update
      (Function.update (Function.update (Function.update w tmp word) o []) o word) tmp [] =
      Function.update w o word := by
    funext i
    by_cases hi : i = tmp
    · subst i
      simp [hto, ht]
    · by_cases hio : i = o
      · subst i
        simp [Ne.symm hto]
      · simp [hi, hio]
  refine ⟨t + (2 * (w o).length + 3 +
      (7 * word.length + 5 + (2 * word.length + 3))), r₄, word, ?_, hv, hl, ?_⟩
  · have hp' := hp
    simp only [Function.update_of_ne hto, Function.update_self] at hp'
    have hc' := hc
    simp only [Function.update_of_ne hto.symm] at hc'
    have hz' := hz
    simp only [Function.update_of_ne hto, Function.update_self] at hz'
    simpa only [replaceCmd, hframe] using he.seq (hc'.seq (hp'.seq hz'))
  · nlinarith

/-- One Horner step for `sum (3*M)^j`, using data 12 for `3*M` and data 5 for one. -/
def hornerStep : Cmd 8 32 :=
  .seq (replaceCmd .multiply 2 12 2 3 (by decide) (by decide))
    (replaceCmd .add 2 5 2 3 (by decide) (by decide))

def horner : ℕ → Cmd 8 32
  | 0 => .base .skip
  | j + 1 => .seq (horner j) hornerStep

theorem hornerStep_eval (r : Regs) (w : Words) (ht : w 3 = []) :
    ∃ t rf word, Eval hornerStep t (state r w)
        (state rf (Function.update w 2 word)) ∧
      toNat word = toNat (w 2) * toNat (w 12) + toNat (w 5) ∧
      word.length ≤ (w 2).length + (w 12).length + (w 5).length + 2 ∧
      t ≤ 1200 * ((w 2).length + (w 12).length + (w 5).length + 2) ^ 2 := by
  obtain ⟨t₁, r₁, word₁, he₁, hv₁, hl₁, ht₁⟩ :=
    replace_eval .multiply r w 2 12 2 3 (by decide) (by decide) (by decide) ht
  obtain ⟨t₂, r₂, word₂, he₂, hv₂, hl₂, ht₂⟩ :=
    replace_eval .add r₁ (Function.update w 2 word₁) 2 5 2 3
      (by decide) (by decide) (by decide) (by simpa using ht)
  simp only [Function.update_self, Function.update_of_ne (by decide : (5 : Fin 19) ≠ 2),
    Arithmetic.value] at hv₂ hl₂ ht₂
  refine ⟨t₁ + t₂, r₂, word₂, ?_, ?_, by omega, ?_⟩
  · simpa only [hornerStep, Function.update_idem] using he₁.seq he₂
  · simpa only [Arithmetic.value, hv₁] using hv₂
  · let L := (w 2).length + (w 12).length + (w 5).length + 2
    have h₁ : 2 * (w 2).length + (w 12).length + 2 ≤ 2 * L := by dsimp [L]; omega
    have h₂ : 2 * word₁.length + (w 5).length + 2 ≤ 2 * L := by dsimp [L]; omega
    have hs₁ := Nat.pow_le_pow_left h₁ 2
    have hs₂ := Nat.pow_le_pow_left h₂ 2
    dsimp [L] at hs₁ hs₂
    nlinarith

/-- Horner's recurrence is unrolled in the finite control. The summation below
counts its actual arithmetic traces, with no unit-cost natural multiplication. -/
theorem horner_eval (j : ℕ) (r : Regs) (w : Words) (ht : w 3 = [])
    (hu : toNat (w 5) = 1) :
    ∃ t rf word, Eval (horner j) t (state r w)
        (state rf (Function.update w 2 word)) ∧
      toNat word = toNat (w 12) ^ j * toNat (w 2) +
        ∑ i ∈ Finset.range j, toNat (w 12) ^ i ∧
      word.length ≤ (w 2).length + j * ((w 12).length + (w 5).length + 2) ∧
      t ≤ 1200 * ∑ i ∈ Finset.range j,
        ((w 2).length + (i + 1) * ((w 12).length + (w 5).length + 2) + 2) ^ 2 := by
  induction j with
  | zero =>
    refine ⟨0, r, w 2, ?_, ?_, ?_, ?_⟩
    · simpa only [horner, Function.update_eq_self] using
        Eval.base (StructuredProgram.Eval.skip (state r w))
    · simp
    · simp
    · simp
  | succ j ih =>
    obtain ⟨t₁, r₁, word₁, he₁, hv₁, hl₁, ht₁⟩ := ih
    obtain ⟨t₂, r₂, word₂, he₂, hv₂, hl₂, ht₂⟩ :=
      hornerStep_eval r₁ (Function.update w 2 word₁) (by simpa using ht)
    simp only [Function.update_self,
      Function.update_of_ne (by decide : (12 : Fin 19) ≠ 2),
      Function.update_of_ne (by decide : (5 : Fin 19) ≠ 2)] at hv₂ hl₂ ht₂
    refine ⟨t₁ + t₂, r₂, word₂, ?_, ?_, ?_, ?_⟩
    · simpa only [horner, Function.update_idem] using he₁.seq he₂
    · rw [hv₂, hu, hv₁, geom_sum_succ, pow_succ]
      ring
    · simp only [Nat.add_mul, Nat.one_mul]
      omega
    · have harg : word₁.length + (w 12).length + (w 5).length + 2 ≤
          (w 2).length + (j + 1) * ((w 12).length + (w 5).length + 2) + 2 := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      have hs := Nat.pow_le_pow_left harg 2
      rw [Finset.sum_range_succ, Nat.mul_add]
      omega

/-- Computes `clog 2 (4*C*M)`, multiplies by Gamma and s, and tests `M < Gamma*h*s`.
Horner evaluation and all arithmetic are finite binary programs. -/
def budgetTest (k : ℕ) : Cmd 8 32 :=
  .seq (multiplyCmd 1 4 12 (by decide) (by decide))
    (.seq (horner (k - 1))
    (.seq (replaceCmd .multiply 2 6 2 3 (by decide) (by decide))
    (.seq (replaceCmd .multiply 2 1 2 3 (by decide) (by decide))
    (.seq (clogCmd 2 10)
    (.seq (multiplyCmd 10 7 11 (by decide) (by decide))
    (.seq (multiplyCmd 11 0 9 (by decide) (by decide))
    (.seq (copyCmd 1 8)
    (.seq (clearCmd 2)
    (.seq (clearCmd 10)
    (.seq (clearCmd 11)
    (.seq (clearCmd 12) (compareCmd 8 9))))))))))))

def prepared (k : ℕ) (s M : List Bool) : Words :=
  fun i => if i = 0 then s else if i = 1 then M else if i = 4 then (3 : ℕ).bits
    else if i = 5 then [true] else if i = 6 then (16 : ℕ).bits
    else if i = 7 then (SparseCharging.rightConstant k).bits else []

def candidateWidth (k : ℕ) (s M : List Bool) : ℕ :=
  (k - 1) * (M.length + 6) + M.length + s.length +
    (SparseCharging.rightConstant k).bits.length + 20

/-- Exact execution of the expensive test, including its arithmetic costs and cleanup. -/
theorem budgetTest_eval (k : ℕ) (hk : 2 ≤ k) (r : Regs) (s M : List Bool)
    (hM : 0 < toNat M) :
    ∃ t rf, Eval (budgetTest k) t (state r (prepared k s M))
        (state rf (prepared k s M)) ∧
      (rf 0 = true ↔ toNat M < SparseCharging.rightConstant k *
        Nat.clog 2 (4 * SparseCharging.depthConstant k (toNat M) * toNat M) * toNat s) ∧
      t ≤ 10000 * (k + 1) * candidateWidth k s M ^ 2 := by
  let w := prepared k s M
  obtain ⟨t₁, r₁, base, he₁, hv₁, hl₁, ht₁⟩ :=
    multiply_eval r w 1 4 12 (by decide) (by decide) (by simp [w, prepared])
  let w₁ := Function.update w 12 base
  obtain ⟨t₂, r₂, sum, he₂, hv₂, hl₂, ht₂⟩ := horner_eval (k - 1) r₁ w₁
    (by simp [w₁, w, prepared])
    (by simp [w₁, w, prepared, BinaryArithmetic.toNat, BinaryArithmetic.bitVal])
  let w₂ := Function.update w₁ 2 sum
  obtain ⟨t₃, r₃, scaled, he₃, hv₃, hl₃, ht₃⟩ :=
    replace_eval .multiply r₂ w₂ 2 6 2 3 (by decide) (by decide) (by decide)
      (by simp [w₂, w₁, w, prepared])
  let w₃ := Function.update w₂ 2 scaled
  obtain ⟨t₄, r₄, arg, he₄, hv₄, hl₄, ht₄⟩ :=
    replace_eval .multiply r₃ w₃ 2 1 2 3 (by decide) (by decide) (by decide)
      (by simp [w₃, w₂, w₁, w, prepared])
  have hbase : toNat base = toNat M * 3 := by
    simpa [w, prepared, ArithmeticExpressionSupport.bits_value] using hv₁
  have hsum : toNat sum = ∑ i ∈ Finset.range (k - 1), (3 * toNat M) ^ i := by
    simpa [w₁, w, prepared, hbase, Nat.mul_comm] using hv₂
  have hscaled : toNat scaled = toNat sum * 16 := by
    simpa [w₂, w₁, w, prepared, Arithmetic.value, ArithmeticExpressionSupport.bits_value] using hv₃
  have harg : toNat arg = 4 * SparseCharging.depthConstant k (toNat M) * toNat M := by
    have hv : toNat arg = toNat scaled * toNat M := by
      simpa [Arithmetic.value, w₃, w₂, w₁, w, prepared] using hv₄
    rw [hv, hscaled, hsum, SparseCharging.depthConstant]
    ring
  have hargpos : 0 < toNat arg := by
    rw [harg]
    have hC : 0 < SparseCharging.depthConstant k (toNat M) := by
      have := SparseBudget.four_le_depthConstant k (toNat M) hk
      omega
    exact Nat.mul_pos (Nat.mul_pos (by decide) hC) hM
  let w₄ := Function.update w₃ 2 arg
  obtain ⟨t₅, r₅, logarithm, he₅, hv₅, hl₅, ht₅⟩ := clog_eval r₄ w₄ 2 10 (by decide)
    (by simp [w₄, w₃, w₂, w₁, w, prepared]) (by simpa [w₄] using hargpos)
  let w₅ := Function.update w₄ 10 logarithm
  obtain ⟨t₆, r₆, product, he₆, hv₆, hl₆, ht₆⟩ :=
    multiply_eval r₅ w₅ 10 7 11 (by decide) (by decide)
      (by simp [w₅, w₄, w₃, w₂, w₁, w, prepared])
  let w₆ := Function.update w₅ 11 product
  obtain ⟨t₇, r₇, threshold, he₇, hv₇, hl₇, ht₇⟩ :=
    multiply_eval r₆ w₆ 11 0 9 (by decide) (by decide)
      (by simp [w₆, w₅, w₄, w₃, w₂, w₁, w, prepared])
  let w₇ := Function.update w₆ 9 threshold
  obtain ⟨r₈, he₈⟩ := copy_eval r₇ w₇ 1 8 (by decide)
    (by simp [w₇, w₆, w₅, w₄, w₃, w₂, w₁, w, prepared])
  let w₈ := Function.update w₇ 8 (w₇ 1)
  obtain ⟨r₉, he₉⟩ := clear_eval r₈ w₈ 2
  let w₉ := Function.update w₈ 2 []
  obtain ⟨r₁₀, he₁₀⟩ := clear_eval r₉ w₉ 10
  let w₁₀ := Function.update w₉ 10 []
  obtain ⟨r₁₁, he₁₁⟩ := clear_eval r₁₀ w₁₀ 11
  let w₁₁ := Function.update w₁₀ 11 []
  obtain ⟨r₁₂, he₁₂⟩ := clear_eval r₁₁ w₁₁ 12
  let w₁₂ := Function.update w₁₁ 12 []
  obtain ⟨rf, he₁₃, hflag⟩ := compare_eval r₁₂ w₁₂ 8 9 (by decide)
  have hframe : Function.update (Function.update w₁₂ 8 []) 9 [] = w := by
    funext i
    fin_cases i <;> simp [w₁₂, w₁₁, w₁₀, w₉, w₈, w₇, w₆, w₅, w₄, w₃, w₂, w₁, w, prepared]
  have hrun := he₁.seq (he₂.seq (he₃.seq (he₄.seq
      (he₅.seq (he₆.seq (he₇.seq (he₈.seq (he₉.seq (he₁₀.seq (he₁₁.seq
        (he₁₂.seq he₁₃)))))))))))
  refine ⟨_, rf, by simpa only [budgetTest, hframe] using hrun, ?_, ?_⟩
  · have hlog : toNat logarithm = Nat.clog 2
        (4 * SparseCharging.depthConstant k (toNat M) * toNat M) := by
      simpa [w₄, harg] using hv₅
    have hprod : toNat product = toNat logarithm * SparseCharging.rightConstant k := by
      simpa [w₅, w₄, w₃, w₂, w₁, w, prepared, ArithmeticExpressionSupport.bits_value] using hv₆
    have hthresh : toNat threshold = SparseCharging.rightConstant k *
        Nat.clog 2 (4 * SparseCharging.depthConstant k (toNat M) * toNat M) * toNat s := by
      simpa [w₆, w₅, w₄, w₃, w₂, w₁, w, prepared, hprod, hlog, Nat.mul_comm] using hv₇
    simpa [w₁₂, w₁₁, w₁₀, w₉, w₈, w₇, w₆, w₅, w₄, w₃, w₂, w₁, w, prepared, hthresh]
      using hflag
  · let L := candidateWidth k s M
    have hL : 20 ≤ L := by dsimp [L, candidateWidth]; omega
    simp [w₆, w₅, w₄, w₃, w₂, w₁, w, prepared] at hl₁ hl₂ hl₃ hl₄ hl₅ hl₆ hl₇
    simp [w₆, w₅, w₄, w₃, w₂, w₁, w, prepared] at ht₁ ht₂ ht₃ ht₄ ht₅ ht₆ ht₇
    have hbase : base.length ≤ M.length + 3 := by simpa using hl₁
    have hH : sum.length ≤ (k - 1) * (M.length + 6) := by
      exact hl₂.trans (Nat.mul_le_mul_left _ (by omega))
    have hsumL : sum.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hscaledL : scaled.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hargL : arg.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hlogL : logarithm.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hprodL : product.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hthreshL : threshold.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hbaseL : base.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hML : M.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hsL : s.length ≤ L := by dsimp [L, candidateWidth]; omega
    have hΓL : (SparseCharging.rightConstant k).bits.length ≤ L := by
      dsimp [L, candidateWidth]; omega
    have hsquare (a b : ℕ) (h : a ≤ b * L) : a ^ 2 ≤ b ^ 2 * L ^ 2 := by
      simpa only [mul_pow] using Nat.pow_le_pow_left h 2
    have hc₁ : t₁ ≤ 100 * L ^ 2 := by
      have harg : M.length + 3 ≤ L := by dsimp [L, candidateWidth]; omega
      have := Nat.pow_le_pow_left harg 2
      nlinarith only [ht₁, this]
    have hc₂ : t₂ ≤ 1200 * (k - 1) * L ^ 2 := by
      have hsum : (∑ i ∈ Finset.range (k - 1), (0 + (i + 1) * (base.length + 1 + 2) + 2) ^ 2) ≤
          (k - 1) * L ^ 2 := by
        calc
          _ ≤ ∑ _i ∈ Finset.range (k - 1), L ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            apply Nat.pow_le_pow_left
            have hi' : i + 1 ≤ k - 1 := by have := Finset.mem_range.mp hi; omega
            have hh := Nat.mul_le_mul hi' (show base.length + 1 + 2 ≤ M.length + 6 by omega)
            dsimp [L, candidateWidth]
            omega
          _ = _ := by simp
      simp only [Nat.zero_add] at hsum
      nlinarith only [ht₂, hsum]
    have hc₃ : t₃ ≤ 1350 * L ^ 2 := by
      have := hsquare (sum.length + 5 + sum.length + 2) 3 (by omega)
      nlinarith only [ht₃, this]
    have hc₄ : t₄ ≤ 2400 * L ^ 2 := by
      have := hsquare (scaled.length + M.length + scaled.length + 2) 4 (by omega)
      nlinarith only [ht₄, this]
    have hc₅ : t₅ ≤ 320 * L ^ 2 := by
      have := hsquare (arg.length + 2) 2 (by omega)
      nlinarith only [ht₅, this]
    have hc₆ : t₆ ≤ 900 * L ^ 2 := by
      have := hsquare (logarithm.length + (SparseCharging.rightConstant k).bits.length + 1)
        3 (by omega)
      nlinarith only [ht₆, this]
    have hc₇ : t₇ ≤ 900 * L ^ 2 := by
      have := hsquare (product.length + s.length + 1) 3 (by omega)
      nlinarith only [ht₇, this]
    have hmax : max M.length threshold.length ≤ L := max_le hML hthreshL
    have hself : L ≤ L ^ 2 := by nlinarith only [hL]
    simp [w₁₂, w₁₁, w₁₀, w₉, w₈, w₇, w₆, w₅, w₄, w₃, w₂, w₁, w, prepared]
    change _ ≤ 10000 * (k + 1) * L ^ 2
    have hkl : (k - 1) * L ^ 2 ≤ k * L ^ 2 := Nat.mul_le_mul_right _ (Nat.sub_le k 1)
    nlinarith only [hc₁, hc₂, hc₃, hc₄, hc₅, hc₆, hc₇, hmax, hself,
      hML, hargL, hlogL, hprodL, hbaseL, hkl, hL]

/-- First test the constant lower bound; the expensive logarithm is evaluated only
when `M >= Gamma`. Both branches return with every temporary word empty. -/
def test (k : ℕ) : Cmd 8 32 :=
  .seq (copyCmd 1 8) (.seq (copyCmd 7 9)
    (.seq (compareCmd 8 9) (.ite 0 (.base .skip) (budgetTest k))))

theorem test_eval (k : ℕ) (hk : 2 ≤ k) (r : Regs) (s M : List Bool)
    (hM : 0 < toNat M) :
    ∃ t rf, Eval (test k) t (state r (prepared k s M))
        (state rf (prepared k s M)) ∧
      (rf 0 = true ↔ toNat M < SparseCharging.rightConstant k ∨
        toNat M < SparseCharging.rightConstant k *
          Nat.clog 2 (4 * SparseCharging.depthConstant k (toNat M) * toNat M) * toNat s) ∧
      t ≤ 12000 * (k + 1) * candidateWidth k s M ^ 2 := by
  let w := prepared k s M
  obtain ⟨r₁, he₁⟩ := copy_eval r w 1 8 (by decide) (by simp [w, prepared])
  let w₁ := Function.update w 8 (w 1)
  obtain ⟨r₂, he₂⟩ := copy_eval r₁ w₁ 7 9 (by decide) (by simp [w₁, w, prepared])
  let w₂ := Function.update w₁ 9 (w₁ 7)
  obtain ⟨r₃, he₃, hf₃⟩ := compare_eval r₂ w₂ 8 9 (by decide)
  have hframe : Function.update (Function.update w₂ 8 []) 9 [] = w := by
    funext i
    fin_cases i <;> simp [w₂, w₁, w, prepared]
  rw [hframe] at he₃
  have hflag : r₃ 0 = true ↔ toNat M < SparseCharging.rightConstant k := by
    simpa [w₂, w₁, w, prepared, ArithmeticExpressionSupport.bits_value] using hf₃
  let L := candidateWidth k s M
  have hL : 20 ≤ L := by dsimp [L, candidateWidth]; omega
  have hML : M.length ≤ L := by dsimp [L, candidateWidth]; omega
  have hΓL : (SparseCharging.rightConstant k).bits.length ≤ L := by
    dsimp [L, candidateWidth]; omega
  have hmax : max M.length (SparseCharging.rightConstant k).bits.length ≤ L :=
    max_le hML hΓL
  have hself : L ≤ L ^ 2 := by nlinarith
  cases hreg : r₃ 0 with
  | false =>
    obtain ⟨t, rf, he, hf, ht⟩ := budgetTest_eval k hk r₃ s M hM
    refine ⟨_, rf, he₁.seq (he₂.seq (he₃.seq (.ite_false hreg he))), ?_, ?_⟩
    · have hn : ¬ toNat M < SparseCharging.rightConstant k := by
        intro h
        have := hflag.mpr h
        simp [hreg] at this
      simpa only [hn, false_or] using hf
    · simp [w₂, w₁, w, prepared]
      change _ ≤ 12000 * (k + 1) * L ^ 2
      change t ≤ 10000 * (k + 1) * L ^ 2 at ht
      nlinarith
  | true =>
    refine ⟨_, r₃, he₁.seq (he₂.seq (he₃.seq (.ite_true hreg
        (Eval.base (StructuredProgram.Eval.skip (state r₃ w)))))), ?_, ?_⟩
    · exact ⟨fun _ => Or.inl (hflag.mp hreg), fun _ => hreg⟩
    · simp [w₂, w₁, w, prepared]
      change _ ≤ 12000 * (k + 1) * L ^ 2
      nlinarith

def dyadicWord : ℕ → List Bool
  | 0 => [true]
  | e + 1 => false :: dyadicWord e

@[simp] theorem dyadicWord_value (e : ℕ) : toNat (dyadicWord e) = 2 ^ e := by
  induction e with
  | zero => simp [dyadicWord, BinaryArithmetic.toNat, BinaryArithmetic.bitVal]
  | succ e ih =>
      simp [dyadicWord, BinaryArithmetic.bitVal, ih, pow_succ,
        Nat.mul_comm]

@[simp] theorem dyadicWord_length (e : ℕ) : (dyadicWord e).length = e + 1 := by
  induction e with
  | zero => rfl
  | succ e ih => simp [dyadicWord, ih]

theorem test_dyadic_eval (k : ℕ) (hk : 2 ≤ k) (r : Regs) (s : List Bool) (e : ℕ) :
    ∃ t rf, Eval (test k) t (state r (prepared k s (dyadicWord e)))
        (state rf (prepared k s (dyadicWord e))) ∧
      (rf 0 = true ↔ SparseBudget.parameterTest k 1 (toNat s) e = false) ∧
      t ≤ 12000 * (k + 1) * candidateWidth k s (dyadicWord e) ^ 2 := by
  obtain ⟨t, rf, he, hf, ht⟩ := test_eval k hk r s (dyadicWord e) (by simp)
  refine ⟨t, rf, he, hf.trans ?_, ht⟩
  have hΓ := SparseBudget.four_le_rightConstant k hk
  simp only [dyadicWord_value, SparseBudget.parameterTest, decide_eq_false_iff_not, one_mul]
  omega

def double : Cmd 8 32 :=
  .seq (.base (.atom (.set 0 false))) (.base (.atom (.push (port 1) 0)))

theorem double_eval (r : Regs) (w : Words) :
    Eval double 2 (state r w)
      (state (Function.update r 0 false) (Function.update w 1 (false :: w 1))) := by
  have hs := Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 8) false) (state r w))
  have hp := Eval.base (StructuredProgram.Eval.atom (.push (port 1) (0 : Fin 8))
    ((StructuredProgram.Atom.set (0 : Fin 8) false).eval (state r w)))
  have h : Eval double 2 (state r w)
      (⟨Function.update r 0 false, Function.update (state r w).stacks (port 1)
        (false :: w 1)⟩ : Data) := by
    simpa [double, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using hs.seq hp
  simpa only [state_update] using h

theorem double_prepared_eval (k : ℕ) (r : Regs) (s : List Bool) (e : ℕ) :
    Eval double 2 (state r (prepared k s (dyadicWord e)))
      (state (Function.update r 0 false) (prepared k s (dyadicWord (e + 1)))) := by
  have h := double_eval r (prepared k s (dyadicWord e))
  have heq : Function.update (prepared k s (dyadicWord e)) 1
      (false :: prepared k s (dyadicWord e) 1) = prepared k s (dyadicWord (e + 1)) := by
    funext i
    by_cases hi : i = 1
    · subst i
      simp [prepared, dyadicWord]
    · simp [hi, prepared]
  simpa only [heq] using h

/-- Termination follows from the proved first-passing index; every loop iteration
is an actual doubling trace followed by the concrete test trace. -/
theorem loop_eval (k : ℕ) (hk : 2 ≤ k) (s : List Bool) (e left : ℕ)
    (hstop : e + left = SparseBudget.chooseExponent k 1 (toNat s) (by decide))
    (r : Regs) (hr : r 0 = true ↔ SparseBudget.parameterTest k 1 (toNat s) e = false) :
    ∃ t rf, Eval (.while 0 (.seq double (test k))) t
        (state r (prepared k s (dyadicWord e)))
        (state rf (prepared k s (dyadicWord
          (SparseBudget.chooseExponent k 1 (toNat s) (by decide))))) ∧
      t ≤ (left + 1) * (12000 * (k + 1) * candidateWidth k s
        (dyadicWord (SparseBudget.chooseExponent k 1 (toNat s) (by decide))) ^ 2 + 3) := by
  induction left generalizing e r with
  | zero =>
    have he : e = SparseBudget.chooseExponent k 1 (toNat s) (by decide) := by omega
    have hp := SparseBudget.chooseExponent_spec k 1 (toNat s) (by decide)
    have hrfalse : r 0 = false := by
      cases h : r 0
      · rfl
      · have hbad := hr.mp h
        rw [he, hp] at hbad
        cases hbad
    refine ⟨1, r, ?_, by omega⟩
    simpa only [he] using Eval.while_false (body := .seq double (test k)) hrfalse
  | succ left ih =>
    have he : e < SparseBudget.chooseExponent k 1 (toNat s) (by decide) := by omega
    have hfail : SparseBudget.parameterTest k 1 (toNat s) e = false := by
      have hn := Nat.find_min (SparseBudget.exists_parameter k 1 (toNat s) (by decide)) he
      cases h : SparseBudget.parameterTest k 1 (toNat s) e
      · rfl
      · exact False.elim (hn h)
    have hd := double_prepared_eval k r s e
    obtain ⟨t, r₁, ht, hf, htime⟩ := test_dyadic_eval k hk (Function.update r 0 false) s (e + 1)
    obtain ⟨u, rf, hu, hutime⟩ := ih (e + 1) (by omega) r₁ hf
    refine ⟨2 + t + u + 1, rf, Eval.while_true (hr.mpr hfail) (hd.seq ht) hu, ?_⟩
    have hwidth : candidateWidth k s (dyadicWord (e + 1)) ≤
        candidateWidth k s (dyadicWord
          (SparseBudget.chooseExponent k 1 (toNat s) (by decide))) := by
      simp only [candidateWidth, dyadicWord_length]
      have hh := Nat.mul_le_mul_left (k - 1)
        (show e + 1 + 1 + 6 ≤
          SparseBudget.chooseExponent k 1 (toNat s) (by decide) + 1 + 6 by omega)
      omega
    have hcost := Nat.mul_le_mul_left (12000 * (k + 1)) (Nat.pow_le_pow_left hwidth 2)
    let C := 12000 * (k + 1) * candidateWidth k s
      (dyadicWord (SparseBudget.chooseExponent k 1 (toNat s) (by decide))) ^ 2
    have htC : t ≤ C := htime.trans (by simpa only [C] using hcost)
    have huC : u ≤ (left + 1) * (C + 3) := by simpa only [C] using hutime
    change 2 + t + u + 1 ≤ (left + 2) * (C + 3)
    calc
      2 + t + u + 1 ≤ 3 + C + (left + 1) * (C + 3) := by omega
      _ = (left + 2) * (C + 3) := by ring

/-- These constants are part of the fixed instruction table chosen from k. -/
def initCmd (k : ℕ) : Cmd 8 32 :=
  .seq (loadCmd 1 [true]) (.seq (loadCmd 4 (3 : ℕ).bits)
    (.seq (loadCmd 5 [true]) (.seq (loadCmd 6 (16 : ℕ).bits)
      (loadCmd 7 (SparseCharging.rightConstant k).bits))))

def inputWords (s : List Bool) : Words := fun i => if i = 0 then s else []

theorem initCmd_eval (k : ℕ) (r : Regs) (s : List Bool) :
    ∃ t rf, Eval (initCmd k) t (state r (inputWords s))
      (state rf (prepared k s (dyadicWord 0))) ∧
      t ≤ 2 * (SparseCharging.rightConstant k).bits.length + 18 := by
  let w := inputWords s
  obtain ⟨r₁, he₁⟩ := load_eval r w 1 [true] (by simp [w, inputWords])
  let w₁ := Function.update w 1 [true]
  obtain ⟨r₂, he₂⟩ := load_eval r₁ w₁ 4 (3 : ℕ).bits (by simp [w₁, w, inputWords])
  let w₂ := Function.update w₁ 4 (3 : ℕ).bits
  obtain ⟨r₃, he₃⟩ := load_eval r₂ w₂ 5 [true] (by simp [w₂, w₁, w, inputWords])
  let w₃ := Function.update w₂ 5 [true]
  obtain ⟨r₄, he₄⟩ := load_eval r₃ w₃ 6 (16 : ℕ).bits
    (by simp [w₃, w₂, w₁, w, inputWords])
  let w₄ := Function.update w₃ 6 (16 : ℕ).bits
  obtain ⟨rf, he₅⟩ := load_eval r₄ w₄ 7 (SparseCharging.rightConstant k).bits
    (by simp [w₄, w₃, w₂, w₁, w, inputWords])
  have hframe : Function.update w₄ 7 (SparseCharging.rightConstant k).bits =
      prepared k s (dyadicWord 0) := by
    funext i
    fin_cases i <;> simp [w₄, w₃, w₂, w₁, w, inputWords, prepared, dyadicWord]
  refine ⟨_, rf, by
    simpa only [initCmd, hframe] using he₁.seq (he₂.seq (he₃.seq (he₄.seq he₅))), ?_⟩
  simp only [bits_three_length, bits_sixteen_length, List.length_singleton]
  omega

/-- The actual dyadic search. The natural-number minimizer appears only in its
specification, never as a machine instruction or a supplied runtime service. -/
def search (k : ℕ) : Cmd 8 32 :=
  .seq (initCmd k) (.seq (test k) (.while 0 (.seq double (test k))))

def searchCost (k : ℕ) (s : List Bool) : ℕ :=
  let N := SparseBudget.chooseExponent k 1 (toNat s) (by decide)
  (N + 3) * (12000 * (k + 1) * candidateWidth k s (dyadicWord N) ^ 2 +
    2 * (SparseCharging.rightConstant k).bits.length + 21)

theorem search_eval (k : ℕ) (hk : 2 ≤ k) (r : Regs) (s : List Bool) :
    ∃ t rf, Eval (search k) t (state r (inputWords s))
      (state rf (prepared k s (dyadicWord
        (SparseBudget.chooseExponent k 1 (toNat s) (by decide))))) ∧
      t ≤ searchCost k s := by
  obtain ⟨t₁, r₁, he₁, ht₁⟩ := initCmd_eval k r s
  obtain ⟨t₂, r₂, he₂, hf₂, ht₂⟩ := test_dyadic_eval k hk r₁ s 0
  obtain ⟨t₃, rf, he₃, ht₃⟩ := loop_eval k hk s 0
    (SparseBudget.chooseExponent k 1 (toNat s) (by decide)) (by omega) r₂ hf₂
  refine ⟨t₁ + (t₂ + t₃), rf, he₁.seq (he₂.seq he₃), ?_⟩
  have hwidth : candidateWidth k s (dyadicWord 0) ≤ candidateWidth k s
      (dyadicWord (SparseBudget.chooseExponent k 1 (toNat s) (by decide))) := by
    simp only [candidateWidth, dyadicWord_length]
    have := Nat.mul_le_mul_left (k - 1)
      (show 0 + 1 + 6 ≤ SparseBudget.chooseExponent k 1 (toNat s) (by decide) + 1 + 6 by omega)
    omega
  have hcost := Nat.mul_le_mul_left (12000 * (k + 1)) (Nat.pow_le_pow_left hwidth 2)
  dsimp [searchCost]
  nlinarith

theorem chooseExponent_input_bits (k : ℕ) :
    ∃ T : ℕ, ∀ s : List Bool, 0 < toNat s →
      SparseBudget.chooseExponent k 1 (toNat s) (by decide) ≤ T + 2 * s.length := by
  obtain ⟨K, T, h⟩ := SparseBudget.choose_encoding_bounds k
  refine ⟨T, ?_⟩
  intro s hs
  have hb := ModularArithmetic.toNat_lt_pow_length s
  have hl := Nat.log_lt_of_lt_pow (ne_of_gt hs) hb
  have hn := (h 1 (toNat s) (by decide) hs).2
  omega

/-- Constants are chosen before the binary input. This is polynomial in encoding
length, not in the integer represented by the input word. -/
theorem searchCost_polynomial (k : ℕ) :
    ∃ K : ℕ, ∀ s : List Bool, 0 < toNat s → searchCost k s ≤ K * (s.length + 1) ^ 3 := by
  obtain ⟨T, hT⟩ := chooseExponent_input_bits k
  let g := (SparseCharging.rightConstant k).bits.length
  let D := (k + 2) * (T + g + 32)
  let E := 12000 * (k + 1) * D ^ 2 + 2 * g + 21
  refine ⟨(T + 5) * E, ?_⟩
  intro s hs
  let N := SparseBudget.chooseExponent k 1 (toNat s) (by decide)
  have hN : N ≤ T + 2 * s.length := hT s hs
  have hN' : N + 3 ≤ (T + 5) * (s.length + 1) := by nlinarith
  have hwidth : candidateWidth k s (dyadicWord N) ≤ D * (s.length + 1) := by
    simp only [candidateWidth, dyadicWord_length]
    have hsub := Nat.mul_le_mul_right (N + 1 + 6) (Nat.sub_le k 1)
    have hscaled := Nat.mul_le_mul_left (k + 1) hN
    have hD₁ : 2 * k + 3 ≤ D := by dsimp [D]; nlinarith
    have hD₂ : (k + 1) * T + 7 * k + g + 21 ≤ D := by dsimp [D]; nlinarith
    have hD₃ := Nat.mul_le_mul_right s.length hD₁
    change _ ≤ D * (s.length + 1)
    change _ + _ + _ + g + _ ≤ _
    nlinarith
  have hsq := Nat.pow_le_pow_left hwidth 2
  have hone : 1 ≤ (s.length + 1) ^ 2 := by nlinarith
  have hconstant := Nat.mul_le_mul_left (2 * g + 21) hone
  have hterm : 12000 * (k + 1) * candidateWidth k s (dyadicWord N) ^ 2 + 2 * g + 21 ≤
      E * (s.length + 1) ^ 2 := by
    dsimp [E]
    rw [mul_pow] at hsq
    have hscaled := Nat.mul_le_mul_left (12000 * (k + 1)) hsq
    nlinarith
  have hprod := Nat.mul_le_mul hN' hterm
  dsimp [searchCost]
  change (N + 3) * _ ≤ _
  calc
    _ ≤ ((T + 5) * (s.length + 1)) * (E * (s.length + 1) ^ 2) := hprod
    _ = (T + 5) * E * (s.length + 1) ^ 3 := by ring

/-- Fixed-k multiplication computes the safe occurrence bound `4*M^(k-1)`. -/
def boundPowers : ℕ → Cmd 8 32
  | 0 => .base .skip
  | j + 1 => .seq (boundPowers j)
      (replaceCmd .multiply 2 1 2 3 (by decide) (by decide))

theorem boundPowers_eval (j : ℕ) (r : Regs) (w : Words) (ht : w 3 = []) :
    ∃ t rf word, Eval (boundPowers j) t (state r w)
        (state rf (Function.update w 2 word)) ∧
      toNat word = toNat (w 2) * toNat (w 1) ^ j ∧
      word.length ≤ (w 2).length + j * ((w 1).length + 1) ∧
      t ≤ 600 * j * ((w 2).length + j * ((w 1).length + 1) + 2) ^ 2 := by
  induction j with
  | zero =>
    refine ⟨0, r, w 2, ?_, ?_, ?_, ?_⟩
    · simpa only [boundPowers, Function.update_eq_self] using
        Eval.base (StructuredProgram.Eval.skip (state r w))
    · simp
    · simp
    · simp
  | succ j ih =>
    obtain ⟨t, r₁, word, he, hv, hl, htime⟩ := ih
    obtain ⟨u, rf, word', he', hv', hl', htime'⟩ := replace_eval .multiply r₁
      (Function.update w 2 word) 2 1 2 3 (by decide) (by decide) (by decide)
      (by simpa using ht)
    simp only [Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 19) ≠ 2), Arithmetic.value] at hv' hl' htime'
    refine ⟨t + u, rf, word', ?_, ?_, ?_, ?_⟩
    · simpa only [boundPowers, Function.update_idem] using he.seq he'
    · rw [hv', hv, pow_succ]
      ring
    · simp only [Nat.add_mul, Nat.one_mul]
      omega
    · have hstep : word.length + (w 1).length + word.length + 2 ≤
          2 * ((w 2).length + (j + 1) * ((w 1).length + 1) + 2) := by
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      have hs := Nat.pow_le_pow_left hstep 2
      have hmono : ((w 2).length + j * ((w 1).length + 1) + 2) ^ 2 ≤
          ((w 2).length + (j + 1) * ((w 1).length + 1) + 2) ^ 2 :=
        Nat.pow_le_pow_left (by simp only [Nat.add_mul, Nat.one_mul]; omega) 2
      have hm := Nat.mul_le_mul_left (600 * j) hmono
      nlinarith

def command (k : ℕ) : Cmd 8 32 :=
  .seq (search k) (.seq (loadCmd 2 (4 : ℕ).bits) (.seq (boundPowers (k - 1))
    (.seq (clearCmd 4) (.seq (clearCmd 5) (.seq (clearCmd 6) (clearCmd 7))))))

def outputWords (s M B : List Bool) : Words :=
  fun i => if i = 0 then s else if i = 1 then M else if i = 2 then B else []

def commandCost (k : ℕ) (s : List Bool) : ℕ :=
  searchCost k s + 600 * k *
    (5 + k * (SparseBudget.chooseExponent k 1 (toNat s) (by decide) + 2)) ^ 2 +
      2 * (SparseCharging.rightConstant k).bits.length + 50

/-- The two parameter words are returned in ports one and two; the input in port
zero is preserved for the calling algorithm. All remaining 29 stacks are empty. -/
theorem command_eval (k : ℕ) (hk : 2 ≤ k) (r : Regs) (s : List Bool) :
    ∃ t rf M B, Eval (command k) t (state r (inputWords s))
        (state rf (outputWords s M B)) ∧
      toNat M = SparseBudget.chooseM k 1 (toNat s) (by decide) ∧
      toNat B = 4 * toNat M ^ (k - 1) ∧ t ≤ commandCost k s := by
  let M := dyadicWord (SparseBudget.chooseExponent k 1 (toNat s) (by decide))
  obtain ⟨t₁, r₁, he₁, ht₁⟩ := search_eval k hk r s
  let w := prepared k s M
  obtain ⟨r₂, he₂⟩ := load_eval r₁ w 2 (4 : ℕ).bits (by simp [w, prepared])
  let w₂ := Function.update w 2 (4 : ℕ).bits
  obtain ⟨t₃, r₃, B, he₃, hv₃, _, ht₃⟩ := boundPowers_eval (k - 1) r₂ w₂
    (by simp [w₂, w, prepared])
  let w₃ := Function.update w₂ 2 B
  obtain ⟨r₄, he₄⟩ := clear_eval r₃ w₃ 4
  let w₄ := Function.update w₃ 4 []
  obtain ⟨r₅, he₅⟩ := clear_eval r₄ w₄ 5
  let w₅ := Function.update w₄ 5 []
  obtain ⟨r₆, he₆⟩ := clear_eval r₅ w₅ 6
  let w₆ := Function.update w₅ 6 []
  obtain ⟨rf, he₇⟩ := clear_eval r₆ w₆ 7
  have hframe : Function.update w₆ 7 [] = outputWords s M B := by
    funext i
    fin_cases i <;> simp [w₆, w₅, w₄, w₃, w₂, w, prepared, outputWords]
  have hrun := he₁.seq (he₂.seq (he₃.seq (he₄.seq (he₅.seq (he₆.seq he₇)))))
  refine ⟨_, rf, M, B, by simpa only [command, hframe] using hrun,
    by simp [M, SparseBudget.chooseM], ?_, ?_⟩
  · simpa [w₂, w, prepared, ArithmeticExpressionSupport.bits_value] using hv₃
  · simp [w₂, w, prepared, M] at ht₃
    let N := SparseBudget.chooseExponent k 1 (toNat s) (by decide)
    have harg : 3 + (k - 1) * (N + 1 + 1) + 2 ≤ 5 + k * (N + 2) := by
      rw [show N + 1 + 1 = N + 2 by omega]
      have := Nat.mul_le_mul_right (N + 2) (Nat.sub_le k 1)
      omega
    have hbudget := Nat.mul_le_mul (Nat.mul_le_mul_left 600 (Nat.sub_le k 1))
      (Nat.pow_le_pow_left harg 2)
    change t₃ ≤ 600 * (k - 1) * (3 + (k - 1) * (N + 1 + 1) + 2) ^ 2 at ht₃
    have htime₃ := ht₃.trans hbudget
    simp [w₆, w₅, w₄, w₃, w₂, w, prepared]
    dsimp [commandCost]
    change _ ≤ searchCost k s + 600 * k * (5 + k * (N + 2)) ^ 2 + _ + _
    omega

theorem commandCost_polynomial (k : ℕ) :
    ∃ K : ℕ, ∀ s : List Bool, 0 < toNat s → commandCost k s ≤ K * (s.length + 1) ^ 3 := by
  obtain ⟨K, hK⟩ := searchCost_polynomial k
  obtain ⟨T, hT⟩ := chooseExponent_input_bits k
  let D := 5 + k * (T + 4)
  let g := (SparseCharging.rightConstant k).bits.length
  refine ⟨K + 600 * k * D ^ 2 + 2 * g + 50, ?_⟩
  intro s hs
  have hsearch := hK s hs
  have hindex := Nat.mul_le_mul_left k (hT s hs)
  have harg : 5 + k * (SparseBudget.chooseExponent k 1 (toNat s) (by decide) + 2) ≤
      D * (s.length + 1) := by
    have hcoef : 2 * k ≤ D := by dsimp [D]; nlinarith
    have hconst : 5 + k * (T + 2) ≤ D := by dsimp [D]; nlinarith
    have hlin := Nat.mul_le_mul_right s.length hcoef
    calc
      _ ≤ (5 + k * (T + 2)) + 2 * k * s.length := by nlinarith
      _ ≤ D + D * s.length := Nat.add_le_add hconst hlin
      _ = D * (s.length + 1) := by ring
  have hsquare := Nat.pow_le_pow_left harg 2
  rw [mul_pow] at hsquare
  have hscaled := Nat.mul_le_mul_left (600 * k) hsquare
  have hpow : (s.length + 1) ^ 2 ≤ (s.length + 1) ^ 3 := by
    exact Nat.pow_le_pow_right (by omega) (by decide)
  have hone : 1 ≤ (s.length + 1) ^ 3 := Nat.one_le_pow' 3 s.length
  have hp := Nat.mul_le_mul_left (600 * k * D ^ 2) hpow
  have hc := Nat.mul_le_mul_left (2 * g + 50) hone
  dsimp [commandCost]
  change _ + _ + 2 * g + 50 ≤ _
  nlinarith

def program (k : ℕ) : Program 8 32 (size (command k) + 1) :=
  compiled (command k) (port 0) (port 1)

/-- One finite Boolean/stack instruction table is chosen from k before the input.
The returned configuration exposes both full parameter words for the caller. -/
theorem program_execution (k : ℕ) (hk : 2 ≤ k) :
    ∃ K : ℕ, ∀ s : List Bool, 0 < toNat s →
      ∃ t rf M B, Trace (program k) t (initial (program k) s)
          ((state rf (outputWords s M B)).withPC none) ∧
        t ≤ K * (s.length + 1) ^ 3 ∧
        toNat M = SparseBudget.chooseM k 1 (toNat s) (by decide) ∧
        toNat B = 4 * toNat M ^ (k - 1) := by
  obtain ⟨K, hK⟩ := commandCost_polynomial k
  refine ⟨K + 1, ?_⟩
  intro s hs
  obtain ⟨t, rf, M, B, he, hM, hB, ht⟩ := command_eval k hk (fun _ => false) s
  have hinput : state (fun _ => false) (inputWords s) =
      (StructuredProgram.ioState (port 0) s : Data) := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      fin_cases i <;> rfl
  have hc := compiled_halt_trace he (port 0) (port 1)
  rw [hinput] at hc
  refine ⟨t + 1, rf, M, B, hc, ?_, hM, hB⟩
  have hb := ht.trans (hK s hs)
  have hp : 1 ≤ (s.length + 1) ^ 3 := Nat.one_le_pow' 3 s.length
  nlinarith

/-- The polynomial-time local parameter search has polynomial storage at every
source prefix, including every arithmetic temporary and every one of its stacks. -/
theorem program_execution_space (k : ℕ) (hk : 2 ≤ k) :
    ∃ K : ℕ, ∀ s : List Bool, 0 < toNat s →
      ∃ t rf M B, Trace (program k) t (initial (program k) s)
          ((state rf (outputWords s M B)).withPC none) ∧
        t ≤ K * (s.length + 1) ^ 3 ∧
        toNat M = SparseBudget.chooseM k 1 (toNat s) (by decide) ∧
        toNat B = 4 * toNat M ^ (k - 1) ∧
        ∀ prefixSteps intermediate, prefixSteps ≤ t →
          Trace (program k) prefixSteps (initial (program k) s) intermediate →
          dataBits intermediate ≤ K * (s.length + 1) ^ 3 := by
  obtain ⟨K, hK⟩ := program_execution k hk
  refine ⟨K + 1, ?_⟩
  intro s hs
  obtain ⟨t, rf, M, B, ht, htime, hM, hB⟩ := hK s hs
  refine ⟨t, rf, M, B, ht, htime.trans ?_, hM, hB, ?_⟩
  · exact Nat.mul_le_mul_right _ (Nat.le_succ K)
  · intro prefixSteps intermediate hp htrace
    have hdata := trace_dataBits (program k) htrace
    rw [initial_dataBits] at hdata
    have hlen : s.length ≤ (s.length + 1) ^ 3 :=
      (Nat.le_succ _).trans (Nat.le_self_pow (by decide : (3 : ℕ) ≠ 0) _)
    calc
      dataBits intermediate ≤ s.length + prefixSteps := hdata
      _ ≤ (s.length + 1) ^ 3 + K * (s.length + 1) ^ 3 :=
        Nat.add_le_add hlen (hp.trans htime)
      _ = (K + 1) * (s.length + 1) ^ 3 := by ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram
