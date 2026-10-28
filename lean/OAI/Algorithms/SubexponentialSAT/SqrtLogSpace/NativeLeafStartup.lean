import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupOuterCostStartupBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeaf

/-! Actual loaded-leaf startup and canonical saved selector parameters. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup

open BitProgram StructuredCalls SqrtLog SqrtLog.LeafOuterProgram

/-- The runtime clause scan and hash arithmetic establish the physical
startup boundary from the actual encoded formula, including padded inputs. -/
theorem start_trace_space (a : Data) (W : ℕ) (records : List (List Bool))
    (hW : ∀ i, (a.stacks i).length ≤ W)
    (hempty : ∀ i : Fin 896, i.val ≤ 782 → a.stacks i = [])
    (hformula : a.stacks 784 = Encoding.encodeList id records) (hm : records ≠ []) :
    ∃ steps b, steps ≤ startBudget W records ∧
      steps ≤ CodeSetupOuterCost.startupConstant * (W + 1) ^ 4 ∧
      Eval start steps a b ∧
      StartReady b (BinaryArithmetic.toNat (a.stacks 785)) records.length
        (BinaryArithmetic.toNat (a.stacks 786)) ∧
      (∀ i : Fin 896, 784 ≤ i.val → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ W + startBudget W records) ∧
      Trace (compiled start 784 788) (steps + 1)
        (a.withPC (some (compiled start 784 788).entry)) (b.withPC none) ∧
      ∀ k c, k ≤ steps + 1 → Trace (compiled start 784 788) k
        (a.withPC (some (compiled start 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤
          W + CodeSetupOuterCost.startupConstant * (W + 1) ^ 4 + 1 := by
  obtain ⟨steps, ht, b, he, hr, hf⟩ := start_eval a W records hW hempty hformula hm
  have hrecords : (Encoding.encodeList id records).length ≤ W := hformula ▸ hW 784
  have hpoly := CodeSetupOuterCost.startBudget_bound W records hrecords
  refine ⟨steps, b, ht, ht.trans hpoly, he, hr, hf, ?_, compiled_halt_trace he 784 788, ?_⟩
  · exact SubexpSetupBoundSpec.wordBound_mono
      (SubexpSetupBoundSpec.eval_wordBound hW he) (Nat.add_le_add_left ht W)
  · intro k c hk hc i
    have hg : (c.stacks i).length ≤ (a.stacks i).length + k := by
      simpa [selectedStackBits] using trace_selectedStackBits _ {i} hc
    have hi := hW i
    omega

/-- Save the selector parameters and physically replace both row widths by
its canonical modulus word before any code rows are serialized. -/
def saveCanonical : Cmd 40 896 :=
  .seq HashGreedyProgram.Initialize.command NativeLeaf.canonicalRowWidth

def saveCanonicalTime (n m L : ℕ) : ℕ :=
  let I := 100 * (HashSelect.loopCap n m + 1) * (L + 1)
  I + 18 * (L + I) + 16

/-- This concrete stage preserves all caller words except its five named
outputs. Unary round production is charged by the actual round value. -/
theorem saveCanonical_eval (a : Data) {n m B L : ℕ} (hm : 0 < m)
    (he : WorkerEmpty a) (hL : ∀ i, (a.stacks i).length ≤ L)
    (hc : BinaryArithmetic.toNat (a.stacks 768) = 3 * m)
    (hd : BinaryArithmetic.toNat (a.stacks 773) = SparseCode.distanceDenom m B)
    (hr : BinaryArithmetic.toNat (a.stacks 774) = HashSelect.loopCap n m) :
    ∃ steps b, steps ≤ saveCanonicalTime n m L ∧ Eval saveCanonical steps a b ∧
      WorkerEmpty b ∧ b.stacks 768 = b.stacks 780 ∧ b.stacks 783 = b.stacks 780 ∧
      BinaryArithmetic.toNat (b.stacks 780) = 3 * m ∧
      (b.stacks 780).length = HashCandidates.digitWidth m ∧
      BinaryArithmetic.toNat (b.stacks 817) = SparseCode.distanceDenom m B ∧
      b.stacks 781 = List.replicate (HashSelect.loopCap n m) true ∧
      (∀ i : Fin 896, i ≠ 768 → i ≠ 780 → i ≠ 781 → i ≠ 783 → i ≠ 817 →
        b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ L + saveCanonicalTime n m L) := by
  have hc' : CounterPrograms.value (a.stacks 768) = 3 * m := by
    rw [CounterPrograms.value_eq_toNat]; exact hc
  obtain ⟨ni, hni, c, hi, hs⟩ := HashGreedyProgram.Initialize.command_eval a L hL
    (he 0) (he 1) (he 767) (by omega)
  rw [CounterPrograms.value_eq_toNat, hr] at hni
  let I := 100 * (HashSelect.loopCap n m + 1) * (L + 1)
  have hcb : ∀ i, (c.stacks i).length ≤ L + I :=
    SubexpSetupBoundSpec.wordBound_mono (SubexpSetupBoundSpec.eval_wordBound hL hi)
      (Nat.add_le_add_left hni L)
  have hcf (i : Fin 896) (h780 : i ≠ 780) (h781 : i ≠ 781) (h817 : i ≠ 817) :
      c.stacks i = a.stacks i := by
    simp [hs, HashGreedyProgram.Initialize.resultStacks, h780, h781, h817]
  have hc767 : c.stacks 767 = [] := (hcf 767 (by decide) (by decide) (by decide)).trans (he 767)
  have hrow := NativeLeaf.canonicalRowWidth_eval c hc767
  let b := NativeLeaf.canonicalRowState c
  have hframe (i : Fin 896) (h768 : i ≠ 768) (h780 : i ≠ 780)
      (h781 : i ≠ 781) (h783 : i ≠ 783) (h817 : i ≠ 817) :
      b.stacks i = a.stacks i :=
    (NativeLeaf.canonicalRowState_frame c i h768 h783).trans (hcf i h780 h781 h817)
  have htime : NativeLeaf.canonicalRowSteps c ≤ 18 * (L + I) + 16 := by
    have h1 := hcb 768
    have h2 := hcb 783
    have h3 := hcb 780
    dsimp [NativeLeaf.canonicalRowSteps]
    omega
  have hmod : BinaryArithmetic.toNat (c.stacks 780) = 3 * m ∧
      (c.stacks 780).length = HashCandidates.digitWidth m := by
    simpa only [hs, CounterPrograms.value_eq_toNat] using
      HashGreedyProgram.Initialize.result_modulus a hm hc'
  refine ⟨ni + NativeLeaf.canonicalRowSteps c, b, ?_, hi.seq hrow, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, hframe, ?_⟩
  · dsimp only [saveCanonicalTime]
    dsimp only [I] at htime
    omega
  · intro i
    have hn (j : Fin 896) (hj : 768 ≤ j.val) : workerStack i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      simp only [workerStack, Fin.val_castAdd] at hv
      have := i.isLt
      omega
    exact (hframe _ (hn 768 (by decide)) (hn 780 (by decide)) (hn 781 (by decide))
      (hn 783 (by decide)) (hn 817 (by decide))).trans (he i)
  · exact (NativeLeaf.canonicalRowState_modulus c).trans
      (NativeLeaf.canonicalRowState_frame c 780 (by decide) (by decide)).symm
  · exact (NativeLeaf.canonicalRowState_width c).trans
      (NativeLeaf.canonicalRowState_frame c 780 (by decide) (by decide)).symm
  · rw [NativeLeaf.canonicalRowState_frame c 780 (by decide) (by decide)]
    exact hmod.1
  · rw [NativeLeaf.canonicalRowState_frame c 780 (by decide) (by decide)]
    exact hmod.2
  · rw [NativeLeaf.canonicalRowState_frame c 817 (by decide) (by decide)]
    simpa [hs, HashGreedyProgram.Initialize.resultStacks] using hd
  · rw [NativeLeaf.canonicalRowState_frame c 781 (by decide) (by decide)]
    simp [hs, HashGreedyProgram.Initialize.resultStacks, CounterPrograms.value_eq_toNat, hr]
  · intro i
    apply (NativeLeaf.canonicalRowState_bound c (L + I) hcb i).trans
    dsimp [saveCanonicalTime, I]
    omega

/-- The fixed startup program scans the loaded clauses and then saves the
actual arithmetic results. It does not assume prepared selector metadata. -/
def canonicalStart : Cmd 40 896 := .seq start saveCanonical

def canonicalStartTime (n m W : ℕ) : ℕ :=
  let S := CodeSetupOuterCost.startupConstant * (W + 1) ^ 4
  S + saveCanonicalTime n m (W + S)

/-- Same-run startup, canonical width and saved round/depth parameters.
All 896 stacks are bounded at every prefix, including padded caller words. -/
theorem canonicalStart_eval (a : Data) {n B W : ℕ} (records : List (List Bool))
    (hW : ∀ i, (a.stacks i).length ≤ W)
    (hempty : ∀ i : Fin 896, i.val ≤ 782 → a.stacks i = [])
    (hformula : a.stacks 784 = Encoding.encodeList id records) (hm : records ≠ [])
    (hn : BinaryArithmetic.toNat (a.stacks 785) = n)
    (hB : BinaryArithmetic.toNat (a.stacks 786) = B) :
    ∃ steps b, steps ≤ canonicalStartTime n records.length W ∧
      Eval canonicalStart steps a b ∧ WorkerEmpty b ∧
      b.stacks 768 = b.stacks 780 ∧ b.stacks 783 = b.stacks 780 ∧
      BinaryArithmetic.toNat (b.stacks 780) = 3 * records.length ∧
      (b.stacks 780).length = HashCandidates.digitWidth records.length ∧
      BinaryArithmetic.toNat (b.stacks 817) = SparseCode.distanceDenom records.length B ∧
      b.stacks 781 = List.replicate (HashSelect.loopCap n records.length) true ∧
      BinaryArithmetic.toNat (b.stacks 782) = records.length ∧
      (∀ i : Fin 896, 784 ≤ i.val → i ≠ 817 → b.stacks i = a.stacks i) ∧
      (∀ i, (b.stacks i).length ≤ W + canonicalStartTime n records.length W) ∧
      Trace (compiled canonicalStart 784 788) (steps + 1)
        (a.withPC (some (compiled canonicalStart 784 788).entry)) (b.withPC none) ∧
      ∀ k c, k ≤ steps + 1 → Trace (compiled canonicalStart 784 788) k
        (a.withPC (some (compiled canonicalStart 784 788).entry)) c →
        ∀ i, (c.stacks i).length ≤ W + canonicalStartTime n records.length W + 1 := by
  obtain ⟨ns, s, _, hns, hes, hs, hsf, hsb, _, _⟩ :=
    start_trace_space a W records hW hempty hformula hm
  rw [hn, hB] at hs
  let S := CodeSetupOuterCost.startupConstant * (W + 1) ^ 4
  have hsb' : ∀ i, (s.stacks i).length ≤ W + S := by
    exact SubexpSetupBoundSpec.wordBound_mono
      (SubexpSetupBoundSpec.eval_wordBound hW hes) (Nat.add_le_add_left hns W)
  obtain ⟨nc, b, hnc, hec, hbempty, hwidth, h783, hmod, hmodlen, hdepth, hrounds, hcf, hcb⟩ :=
    saveCanonical_eval s (List.length_pos_iff.mpr hm) hs.worker hsb' hs.count hs.depth hs.rounds
  have heval : Eval canonicalStart (ns + nc) a b := hes.seq hec
  have ht := Nat.add_le_add hns hnc
  change ns + nc ≤ canonicalStartTime n records.length W at ht
  refine ⟨ns + nc, b, ht, heval, hbempty, hwidth, h783, hmod, hmodlen, hdepth, hrounds,
    ?_, ?_, ?_, compiled_halt_trace heval 784 788, ?_⟩
  · rw [hcf 782 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hs.clauses
  · intro i hi hi817
    have hne (j : Fin 896) (hj : j.val < 784) : i ≠ j := by
      intro h
      have hv := congrArg Fin.val h
      omega
    exact (hcf i (hne 768 (by decide)) (hne 780 (by decide)) (hne 781 (by decide))
      (hne 783 (by decide)) hi817).trans (hsf i hi)
  · intro i
    have hb := hcb i
    dsimp only [canonicalStartTime, S] at hb ⊢
    omega
  · intro k c hk hc i
    have hg : (c.stacks i).length ≤ (a.stacks i).length + k := by
      simpa [selectedStackBits] using trace_selectedStackBits _ {i} hc
    have hi := hW i
    omega

/-- A fixed fifth-degree bound covers the entire canonical startup and
all of its temporary words. The numerical ambient dimension is explicit. -/
theorem canonicalStartTime_polynomial (n m W : ℕ) :
    W + canonicalStartTime n m W + 1 ≤
      6000 * (CodeSetupOuterCost.startupConstant + 1) * (n + m + W + 1) ^ 5 := by
  let C := CodeSetupOuterCost.startupConstant
  let X := n + m + W + 1
  let S := C * (W + 1) ^ 4
  let L := W + S
  let I := 100 * (HashSelect.loopCap n m + 1) * (L + 1)
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hsize : Nat.size m ≤ m := Nat.size_le.mpr Nat.lt_two_pow_self
  have hK : HashSelect.loopCap n m + 1 ≤ 3 * X := by
    dsimp [HashSelect.loopCap, X]
    omega
  have hS : S ≤ C * X ^ 4 := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_left (by dsimp [X]; omega) 4)
  have hlinear : W + 1 ≤ X ^ 4 :=
    (show W + 1 ≤ X by dsimp [X]; omega).trans (Nat.le_self_pow (by decide) X)
  have hL : L + 1 ≤ (C + 1) * X ^ 4 := by dsimp [L]; nlinarith only [hS, hlinear]
  have hI : I ≤ 300 * (C + 1) * X ^ 5 := by
    calc
      I ≤ 100 * (3 * X) * ((C + 1) * X ^ 4) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 100 hK) hL
      _ = _ := by rw [pow_succ]; ring
  have hL5 : L + 1 ≤ (C + 1) * X ^ 5 := hL.trans
    (Nat.mul_le_mul_left (C + 1) (Nat.pow_le_pow_right hX (by decide : 4 ≤ 5)))
  change W + (S + (I + 18 * (L + I) + 16)) + 1 ≤ 6000 * (C + 1) * X ^ 5
  have hLdef : L = W + S := rfl
  nlinarith only [hI, hL5, hLdef]

/-- Fixed ordinary-polynomial transport across actual canonical startup and
metadata production. The incoming binary lengths are bounded by the proved
startup boundary, rather than by any exponential search duration. -/
theorem canonicalParameterTime_polynomial :
    ∃ C d : ℕ, ∀ n m B W ml Bl, 0 < m → 0 < B →
      ml ≤ W + canonicalStartTime n m W → Bl ≤ W + canonicalStartTime n m W →
      W + canonicalStartTime n m W +
        parameterTime m B (W + canonicalStartTime n m W) ml Bl + 1 ≤
          C * (n + m + W + 16) ^ d := by
  obtain ⟨C, d, hC⟩ := parameterTime_polynomial
  let A := 6000 * (CodeSetupOuterCost.startupConstant + 1)
  refine ⟨C * (A + 1) ^ d, 5 * d, ?_⟩
  intro n m B W ml Bl hm hB hml hBl
  let U := W + canonicalStartTime n m W
  let X := n + m + W + 16
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hU : U + 1 ≤ A * X ^ 5 :=
    (canonicalStartTime_polynomial n m W).trans
      (Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by dsimp [X]; omega) 5))
  have hmX : m + 15 ≤ X ^ 5 :=
    (show m + 15 ≤ X by dsimp [X]; omega).trans (Nat.le_self_pow (by decide) X)
  have hinput : m + U + 16 ≤ (A + 1) * X ^ 5 := by nlinarith only [hU, hmX]
  calc
    _ ≤ C * (m + U + 16) ^ d := hC m B U ml Bl hm hB hml hBl
    _ ≤ C * ((A + 1) * X ^ 5) ^ d :=
      Nat.mul_le_mul_left C (Nat.pow_le_pow_left hinput d)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup
