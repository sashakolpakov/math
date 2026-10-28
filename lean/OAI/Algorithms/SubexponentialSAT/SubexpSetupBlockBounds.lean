import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSetupStorageCost
import OAI.Algorithms.SubexponentialSAT.SubexpSetupPhaseBlock
import OAI.Algorithms.SubexponentialSAT.SubexpSetupPhaseTail

namespace OAI.Algorithms

/-! Polynomial bounds for the actual block, dimension, and tail setup phases. -/

namespace SubexponentialSAT.SubexpSetupBlockBounds

noncomputable section

open BitProgram StructuredCalls SubexpSetupProgram SubexpSetupStorage

private theorem wordBound_mono {r s B C : ℕ} {a : State r s}
    (h : B ≤ C) (ha : WordBound B a) : WordBound C a :=
  fun i => (ha i).trans h

private theorem transfer (c : Config) (cmd : Cmd 16 (stackCount c))
    (a : SetupState c) (T : ℕ)
    (h : ∃ t b, Eval cmd t a b ∧ t ≤ T ∧ WordBound T b)
    {t : ℕ} {b : SetupState c} (he : Eval cmd t a b) : t ≤ T ∧ WordBound T b := by
  obtain ⟨u, d, hu, hut, hud⟩ := h
  have ht := SubexpPrimeProgram.eval_steps_unique he hu (persistent c 0) (persistent c 0)
  have hb := SubexpPrimeProgram.eval_result_unique he hu (persistent c 0) (persistent c 0)
  simpa only [ht, hb] using And.intro hut hud

private theorem block_output_bound (k : ℕ) (s d Q : List Bool)
    (rf : Fin 8 → Bool) (w : SubexpBlockParameterProgram.Words)
    (ho : SubexpBlockParameterProgram.Output k s d Q w) :
    WordBound (16 * SubexpBlockParameterProgram.commonWidth
      (SubexpBlockParameterProgram.inputWidth k s d Q)
      (SubexpBlockParameterProgram.exponentValue d Q))
      (SubexpBlockParameterProgram.state rf w) := by
  intro i
  change (if h : i.val < 15 then w ⟨i.val, h⟩ else []).length ≤ _
  split
  · exact ho.word_length _
  · exact Nat.zero_le _

def blockCoefficient (c : Config) : ℕ :=
  let A := c.k.bits.length + 5
  1000000 * A ^ 2 + 194 * (16 * A + 1) + 16 * A + 2

theorem block_bounded_run (c : Config) (B P : ℕ) (a : SetupState c)
    (ha : WordBound B a)
    (hE : SubexpBlockParameterProgram.exponentValue
      (a.stacks (persistent c 16)) (a.stacks (persistent c 17)) ≤ P) :
    ∃ t b, Eval (block c) t a b ∧
      t ≤ blockCoefficient c * (B + P + 1) ^ 4 ∧
      WordBound (blockCoefficient c * (B + P + 1) ^ 4) b := by
  let X := B + P + 1
  let A := c.k.bits.length + 5
  let W := SubexpBlockParameterProgram.inputWidth c.k
    (a.stacks (persistent c 4)) (a.stacks (persistent c 16)) (a.stacks (persistent c 17))
  let E := SubexpBlockParameterProgram.exponentValue
    (a.stacks (persistent c 16)) (a.stacks (persistent c 17))
  let M := 16 * A * X ^ 2
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hBX : B ≤ X := by dsimp [X]; omega
  have hEX : E + 1 ≤ X := by dsimp [E, X]; omega
  have hW : W + 1 ≤ A * X := by
    have hs := ha (persistent c 4)
    have hd := ha (persistent c 16)
    have hq := ha (persistent c 17)
    have hk := Nat.mul_le_mul_left (c.k.bits.length + 2) hX
    dsimp [W, SubexpBlockParameterProgram.inputWidth, A]
    nlinarith
  have hX2 : X ≤ X ^ 2 := Nat.le_self_pow (by decide) X
  have h24 : X ^ 2 ≤ X ^ 4 := Nat.pow_le_pow_right hX (by decide)
  have h14 : 1 ≤ X ^ 4 := Nat.one_le_pow _ _ hX
  have hM : B ≤ M := by
    have hx := hBX.trans hX2
    have hc : 1 ≤ 16 * A := by omega
    exact hx.trans (by simpa only [one_mul] using Nat.mul_le_mul_right (X ^ 2) hc)
  obtain ⟨u, rf, w, hu, ho, he⟩ := SubexpSetupPhaseBlock.block_eval c a
  have hlocal : u ≤ (1000000 * A ^ 2 + 1) * X ^ 4 := by
    calc
      u ≤ SubexpBlockParameterProgram.runtimeBound c.k
          (a.stacks (persistent c 4)) (a.stacks (persistent c 16))
          (a.stacks (persistent c 17)) + 1 := hu
      _ ≤ 1000000 * (E + 1) ^ 2 * (W + 1) ^ 2 + 1 :=
        Nat.add_le_add_right (SubexpBlockParameterProgram.runtimeBound_polynomial _ _ _ _) 1
      _ ≤ 1000000 * X ^ 2 * (A * X) ^ 2 + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul
          (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hEX 2))
          (Nat.pow_le_pow_left hW 2)) 1
      _ = 1000000 * A ^ 2 * X ^ 4 + 1 := by ring
      _ ≤ (1000000 * A ^ 2 + 1) * X ^ 4 := by nlinarith
  have hw : WordBound M (SubexpBlockParameterProgram.state rf w) := by
    apply wordBound_mono _ (block_output_bound _ _ _ _ rf w ho)
    change 16 * ((E + 1) * (W + 1)) ≤ M
    calc
      16 * ((E + 1) * (W + 1)) ≤ 16 * (X * (A * X)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hEX hW)
      _ = M := by dsimp [M]; ring
  have hc := stageCost_le c (registerPort (show 8 ≤ 9 by decide))
    (SubexpSetupPhaseBlock.blockFit c) (SubexpSetupPhaseBlock.blockInputs c)
    (SubexpSetupPhaseBlock.blockOutputs c) a (SubexpBlockParameterProgram.state rf w) u M
    (SubexpSetupPhaseBlock.block_inputs_protected c)
    (SubexpSetupPhaseBlock.block_outputs_protected c)
    (by simp [SubexpSetupPhaseBlock.blockInputs])
    (SubexpSetupPhaseBlock.block_outputs_nodup c) (wordBound_mono hM ha) hw
  have hr := returned_wordBound c (registerPort (show 8 ≤ 9 by decide))
    (SubexpSetupPhaseBlock.blockFit c) (SubexpSetupPhaseBlock.blockInputs c)
    (SubexpSetupPhaseBlock.blockOutputs c) a (SubexpBlockParameterProgram.state rf w) M
    (SubexpSetupPhaseBlock.block_inputs_protected c)
    (SubexpSetupPhaseBlock.block_outputs_protected c)
    (by simp [SubexpSetupPhaseBlock.blockInputs])
    (SubexpSetupPhaseBlock.block_outputs_nodup c) (wordBound_mono hM ha) hw
  have hover : storageOverhead 22 3 2 M ≤ 194 * (16 * A + 1) * X ^ 4 := by
    have h12 : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ hX
    have hm : M + 1 ≤ (16 * A + 1) * X ^ 2 := by dsimp [M]; nlinarith
    calc
      storageOverhead 22 3 2 M ≤ 194 * (M + 1) := storageOverhead_linear 22 3 2 M
      _ ≤ 194 * ((16 * A + 1) * X ^ 2) := Nat.mul_le_mul_left _ hm
      _ ≤ 194 * ((16 * A + 1) * X ^ 4) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h24)
      _ = 194 * (16 * A + 1) * X ^ 4 := by ring
  have hout : M ≤ blockCoefficient c * X ^ 4 := by
    have hcoef : 16 * A ≤ blockCoefficient c := by dsimp [blockCoefficient, A]; omega
    exact Nat.mul_le_mul hcoef h24
  refine ⟨SubexpSetupPhaseBlock.blockCost c a rf w u,
    SubexpSetupPhaseBlock.blockResult c a rf w, he, ?_, wordBound_mono hout hr⟩
  have hc' : SubexpSetupPhaseBlock.blockCost c a rf w u ≤ u + storageOverhead 22 3 2 M := by
    simpa only [SubexpSetupPhaseBlock.blockCost, SubexpSetupPhaseBlock.blockInputs,
      SubexpSetupPhaseBlock.blockOutputs, List.length_cons, List.length_nil] using hc
  calc
    SubexpSetupPhaseBlock.blockCost c a rf w u ≤ u + storageOverhead 22 3 2 M := hc'
    _ ≤ (1000000 * A ^ 2 + 1) * X ^ 4 + 194 * (16 * A + 1) * X ^ 4 :=
      Nat.add_le_add hlocal hover
    _ ≤ blockCoefficient c * X ^ 4 := by
      have hcoef : (1000000 * A ^ 2 + 1) + 194 * (16 * A + 1) ≤ blockCoefficient c := by
        dsimp [blockCoefficient, A]
        omega
      simpa only [Nat.add_mul] using Nat.mul_le_mul_right (X ^ 4) hcoef

theorem block_envelope (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ B P a t b,
      WordBound B a →
      SubexpBlockParameterProgram.exponentValue
        (a.stacks (persistent c 16)) (a.stacks (persistent c 17)) ≤ P →
      Eval (block c) t a b →
      t ≤ C * (B + P + 1) ^ q ∧ WordBound (C * (B + P + 1) ^ q) b := by
  refine ⟨blockCoefficient c, 4, ?_, by decide, ?_⟩
  · dsimp [blockCoefficient]; omega
  · intro B P a t b ha hp he
    exact transfer c (block c) a _ (block_bounded_run c B P a ha hp) he

private theorem ceiling_output_bound (u input : List Bool) (out : State 8 8)
    (ho : SubexpCeilingProgram.Output u input out) :
    WordBound (u.length + input.length + 1) out := by
  have base (j : Fin 8) :
      (ModularQuotientPrograms.quotientStacks
        (ModularQuotientArithmetic.divide u input).2 u []
        (ModularQuotientArithmetic.divide u input).1 j).length ≤ u.length + input.length + 1 := by
    fin_cases j <;> simp [ModularQuotientPrograms.quotientStacks,
      ModularQuotientArithmetic.divide_quotient_length,
      ModularArithmetic.reduce_length] <;> omega
  intro j
  by_cases hj : j = 7
  · subst j
    exact ho.2.1.trans (by omega)
  · rw [ho.2.2 j hj]
    exact base j

theorem dimension_bounded_run (c : Config) (B P : ℕ) (a : SetupState c)
    (ha : WordBound B a) (hu : 0 < BinaryArithmetic.toNat (a.stacks (persistent c 5))) :
    ∃ t b, Eval (dimension c) t a b ∧ t ≤ 1000 * (B + P + 1) ^ 2 ∧
      WordBound (1000 * (B + P + 1) ^ 2) b := by
  let X := B + P + 1
  change ∃ t b, Eval (dimension c) t a b ∧ t ≤ 1000 * X ^ 2 ∧
    WordBound (1000 * X ^ 2) b
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hB : B + 1 ≤ X := by dsimp [X]; omega
  have hX2 : X ≤ X ^ 2 := Nat.le_self_pow (by decide) X
  have h12 : 1 ≤ X ^ 2 := hX.trans hX2
  obtain ⟨u, out, ht, ho, he⟩ := SubexpSetupPhaseBlock.dimension_eval c a hu
  have hw : WordBound (3 * X) out := wordBound_mono
    (by have h1 := ha (persistent c 5); have h2 := ha (persistent c 2); omega)
    (ceiling_output_bound _ _ out ho)
  have ha' : WordBound (3 * X) a := wordBound_mono (by omega) ha
  have hc := stageCost_le c (registerPort (show 8 ≤ 9 by decide))
    (SubexpSetupPhaseBlock.dimensionFit c) (SubexpSetupPhaseBlock.dimensionInputs c)
    (SubexpSetupPhaseBlock.dimensionOutputs c) a out u (3 * X)
    (SubexpSetupPhaseBlock.dimension_inputs_protected c)
    (SubexpSetupPhaseBlock.dimension_outputs_protected c)
    (by simp [SubexpSetupPhaseBlock.dimensionInputs])
    (by simp [SubexpSetupPhaseBlock.dimensionOutputs]) ha' hw
  have hr := returned_wordBound c (registerPort (show 8 ≤ 9 by decide))
    (SubexpSetupPhaseBlock.dimensionFit c) (SubexpSetupPhaseBlock.dimensionInputs c)
    (SubexpSetupPhaseBlock.dimensionOutputs c) a out (3 * X)
    (SubexpSetupPhaseBlock.dimension_inputs_protected c)
    (SubexpSetupPhaseBlock.dimension_outputs_protected c)
    (by simp [SubexpSetupPhaseBlock.dimensionInputs])
    (by simp [SubexpSetupPhaseBlock.dimensionOutputs]) ha' hw
  have ht' : u ≤ 500 * X ^ 2 := ht.trans
    ((SubexpCeilingProgram.runtimeBound_le _ _ (ha _) (ha _)).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB 2)))
  have hc' : SubexpSetupPhaseBlock.dimensionCost c a out u ≤ u + storageOverhead 8 2 1 (3 * X) := by
    simpa only [SubexpSetupPhaseBlock.dimensionCost, SubexpSetupPhaseBlock.dimensionInputs,
      SubexpSetupPhaseBlock.dimensionOutputs, List.length_cons, List.length_nil] using hc
  have hov : storageOverhead 8 2 1 (3 * X) ≤ 372 * X ^ 2 := by
    have harg : 3 * X + 1 ≤ 4 * X ^ 2 := by
      have h := Nat.add_le_add (Nat.mul_le_mul_left 3 hX2) h12
      simpa only [show 4 = 3 + 1 by rfl, Nat.add_mul, one_mul] using h
    calc
      storageOverhead 8 2 1 (3 * X) ≤ 93 * (3 * X + 1) :=
        storageOverhead_linear 8 2 1 (3 * X)
      _ ≤ 93 * (4 * X ^ 2) := Nat.mul_le_mul_left _ harg
      _ = 372 * X ^ 2 := by ring
  have hword : 3 * X ≤ 1000 * X ^ 2 :=
    (Nat.mul_le_mul_left 3 hX2).trans
      (Nat.mul_le_mul_right (X ^ 2) (by decide : 3 ≤ 1000))
  refine ⟨SubexpSetupPhaseBlock.dimensionCost c a out u,
    SubexpSetupPhaseBlock.dimensionResult c a out, he, ?_, wordBound_mono hword hr⟩
  exact hc'.trans ((Nat.add_le_add ht' hov).trans (by omega))

theorem dimension_envelope (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ B P a t b,
      WordBound B a → 0 < BinaryArithmetic.toNat (a.stacks (persistent c 5)) →
      Eval (dimension c) t a b →
      t ≤ C * (B + P + 1) ^ q ∧ WordBound (C * (B + P + 1) ^ q) b := by
  refine ⟨1000, 2, by decide, by decide, ?_⟩
  intro B P a t b ha hu he
  exact transfer c (dimension c) a _ (dimension_bounded_run c B P a ha hu) he

private theorem tail_start_bound (c : Config) (B : ℕ) (a : SetupState c)
    (ha : WordBound B a) : WordBound B (SubexpSetupPhaseTail.localState c a) := by
  intro i
  fin_cases i <;> first | exact ha _ | exact Nat.zero_le _

private theorem tail_result_bound (c : Config) (B : ℕ) (a : SetupState c)
    (rf : Fin 8 → Bool) (square tail : List Bool) (ha : WordBound B a)
    (hs : square.length ≤ B) (ht : tail.length ≤ B) :
    WordBound B (SubexpSetupPhaseTail.localResult c a rf square tail) := by
  intro i
  by_cases hi5 : i = 5
  · subst i
    simpa only [SubexpSetupPhaseTail.localResult, Function.update_self] using ht
  by_cases hi4 : i = 4
  · subst i
    simpa [SubexpSetupPhaseTail.localResult] using hs
  simpa only [SubexpSetupPhaseTail.localResult, Function.update_of_ne hi5,
    Function.update_of_ne hi4] using tail_start_bound c B a ha i

theorem tail_bounded_run (c : Config) (B P : ℕ) (a : SetupState c)
    (ha : WordBound B a) :
    ∃ t b, Eval (tailOperands c) t a b ∧ t ≤ 200000 * (B + P + 1) ^ 2 ∧
      WordBound (200000 * (B + P + 1) ^ 2) b := by
  let X := B + P + 1
  change ∃ t b, Eval (tailOperands c) t a b ∧ t ≤ 200000 * X ^ 2 ∧
    WordBound (200000 * X ^ 2) b
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hB : B + 1 ≤ X := by dsimp [X]; omega
  have hX2 : X ≤ X ^ 2 := Nat.le_self_pow (by decide) X
  have h12 : 1 ≤ X ^ 2 := hX.trans hX2
  obtain ⟨u, rf, square, tail, ht, he, _, _, hs, hh⟩ := SubexpSetupPhaseTail.eval c a
  have hs' : square.length ≤ 8 * X := by
    have := ha (persistent c 25)
    omega
  have hh' : tail.length ≤ 8 * X := by
    have h1 := ha (persistent c 17)
    have h2 := ha (persistent c 16)
    have h3 := ha (persistent c 4)
    omega
  have ha' : WordBound (8 * X) a := wordBound_mono (by omega) ha
  have hw := tail_result_bound c (8 * X) a rf square tail ha' hs' hh'
  have hc := stageCost_le c (registerPort (show 8 ≤ 9 by decide))
    (SubexpSetupPhaseTail.fits c) (SubexpSetupPhaseTail.inputs c)
    (SubexpSetupPhaseTail.outputs c) a
    (SubexpSetupPhaseTail.localResult c a rf square tail) u (8 * X)
    (SubexpSetupPhaseTail.inputs_protected c) (SubexpSetupPhaseTail.outputs_protected c)
    (by simp [SubexpSetupPhaseTail.inputs]) (SubexpSetupPhaseTail.outputs_nodup c) ha' hw
  have hr := returned_wordBound c (registerPort (show 8 ≤ 9 by decide))
    (SubexpSetupPhaseTail.fits c) (SubexpSetupPhaseTail.inputs c)
    (SubexpSetupPhaseTail.outputs c) a
    (SubexpSetupPhaseTail.localResult c a rf square tail) (8 * X)
    (SubexpSetupPhaseTail.inputs_protected c) (SubexpSetupPhaseTail.outputs_protected c)
    (by simp [SubexpSetupPhaseTail.inputs]) (SubexpSetupPhaseTail.outputs_nodup c) ha' hw
  have hwidth : SubexpGuardTailProgram.width (SubexpSetupPhaseTail.localState c a) ≤ 8 * X := by
    have h1 := ha (persistent c 25)
    have h2 := ha (persistent c 17)
    have h3 := ha (persistent c 16)
    have h4 := ha (persistent c 4)
    change (a.stacks (persistent c 25)).length + (a.stacks (persistent c 17)).length +
      (a.stacks (persistent c 16)).length + (a.stacks (persistent c 4)).length + 8 ≤ 8 * X
    omega
  have ht' : u ≤ 128001 * X ^ 2 := by
    have hp := Nat.pow_le_pow_left hwidth 2
    calc
      u ≤ 2000 * SubexpGuardTailProgram.width (SubexpSetupPhaseTail.localState c a) ^ 2 + 1 := ht
      _ ≤ 2000 * (8 * X) ^ 2 + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ hp) 1
      _ ≤ 2000 * (8 * X) ^ 2 + X ^ 2 := Nat.add_le_add_left h12 _
      _ = 128001 * X ^ 2 := by ring
  have hc' : SubexpSetupPhaseTail.cost c a rf square tail u ≤
      u + storageOverhead 14 4 2 (8 * X) := by
    simpa only [SubexpSetupPhaseTail.cost, SubexpSetupPhaseTail.inputs,
      SubexpSetupPhaseTail.outputs, List.length_cons, List.length_nil] using hc
  have hov : storageOverhead 14 4 2 (8 * X) ≤ 1377 * X ^ 2 := by
    have harg : 8 * X + 1 ≤ 9 * X ^ 2 := by
      have h := Nat.add_le_add (Nat.mul_le_mul_left 8 hX2) h12
      simpa only [show 9 = 8 + 1 by rfl, Nat.add_mul, one_mul] using h
    calc
      storageOverhead 14 4 2 (8 * X) ≤ 153 * (8 * X + 1) :=
        storageOverhead_linear 14 4 2 (8 * X)
      _ ≤ 153 * (9 * X ^ 2) := Nat.mul_le_mul_left _ harg
      _ = 1377 * X ^ 2 := by ring
  have hword : 8 * X ≤ 200000 * X ^ 2 :=
    (Nat.mul_le_mul_left 8 hX2).trans
      (Nat.mul_le_mul_right (X ^ 2) (by decide : 8 ≤ 200000))
  refine ⟨SubexpSetupPhaseTail.cost c a rf square tail u,
    SubexpSetupPhaseTail.result c a rf square tail, he, ?_, wordBound_mono hword hr⟩
  exact hc'.trans ((Nat.add_le_add ht' hov).trans (by omega))

theorem tail_envelope (c : Config) :
    ∃ C q : ℕ, 1 ≤ C ∧ 1 ≤ q ∧ ∀ B P a t b,
      WordBound B a → Eval (tailOperands c) t a b →
      t ≤ C * (B + P + 1) ^ q ∧ WordBound (C * (B + P + 1) ^ q) b := by
  refine ⟨200000, 2, by decide, by decide, ?_⟩
  intro B P a t b ha he
  exact transfer c (tailOperands c) a _ (tail_bounded_run c B P a ha) he

end
end SubexponentialSAT.SubexpSetupBlockBounds

end OAI.Algorithms
