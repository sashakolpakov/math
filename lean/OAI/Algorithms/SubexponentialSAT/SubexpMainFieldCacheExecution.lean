import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainFieldCacheCore

namespace OAI.Algorithms

/-! Actual execution and selected-field meanings of the Main cache phase. -/

namespace SubexponentialSAT.SubexpMainFieldCacheCore

open BitProgram StructuredCalls
open BinaryArithmetic SubexpLiftRing SubexpQuarticRing
open SubexpCRTCofactorControl
open SubexpQuarticFlatMul (flat)
open SubexpFieldCacheInterpretation (fieldValue)

structure Values (p : ℕ) [Fact p.Prime]
    (ys : List (Quad (Word (baseWidth p 1))))
    (rows : List (List (Quad (Word (baseWidth p 1))))) : Prop where
  inverses : List.Forall₂ (fun a b => fieldValue p b = (fieldValue p a)⁻¹)
    (SubexpNodeLiftData.nodeQuads p) ys
  differences : List.Forall₂ (fun a row => List.Forall₂
    (fun b inverse => fieldValue p inverse = (fieldValue p a - fieldValue p b)⁻¹)
    (SubexpNodeLiftData.nodeQuads p) row) (SubexpNodeLiftData.nodeQuads p) rows
  inverse_length : (ys.flatMap flat).length = 4 * baseWidth p 1 * (p^4 - 1)
  difference_length : (rows.flatten.flatMap flat).length =
    4 * baseWidth p 1 * (p^4 - 1) * (p^4 - 1)

theorem command_value (a : Data) (p : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (h : Ready a p coeff hc) (hexp : BinaryArithmetic.toNat (a.stacks 139) = p^4 - 2) :
    ∃ n ys rows, n + 1 ≤ runtimeBound a p ∧ Values p ys rows ∧
      Eval command n a (output a p ys rows) := by
  let prepared := SubexpPreparedQuarticSetup.preparedData p 0 coeff hc
  let base := sourceWords p coeff hc
  have hs := save_eval a (h.empty 0 (by left; constructor <;> decide))
    (h.empty 138 (by right; constructor <;> decide))
  have he : (saved a).stacks 139 = a.stacks 139 := by simp [saved]
  have hsource : sourceFrame p 97 = ProgramEncoding.encodeRecords
      ((SubexpNodeLiftData.nodeQuads p).map flat) := by
    simp only [sourceFrame, Function.update_same,
      SubexpFieldCacheInterpretation.nodeQuads_flat_encoded]
  have hsourcePort : ∀ i, (139 : Fin 140) ≠ ports i := by
    intro i hh
    have hh' := congrArg Fin.val hh
    change 139 = (SubexpFieldCacheLoad.ordinaryPorts i).val at hh'
    have hb := (SubexpFieldCacheLoad.ordinaryPorts i).isLt
    omega
  have hB : 0 < baseWidth p 1 := Nat.mul_pos (by decide) (Nat.succ_pos _)
  obtain ⟨n, rf, ys, rows, hn, hys, hrows, ht⟩ :=
    SubexpFieldCacheLoad.command_value registers ports 139 hsourcePort p 1
      prepared.modulus (QuarticSearch.liftedCoefficients p 1)
      prepared.reduction prepared.one (SubexpPreparedQuarticSetup.minusOne p 1)
      prepared.reduction_spec prepared.one_spec base rfl rfl rfl rfl
      (SubexpPreparedQuarticPrelude.widthWord_length p 1) rfl rfl hB
      (SubexpNodeLiftData.nodeQuads p) (saved a) (sourceFrame p) hsource
      (by simp [sourceFrame]) (by simp [sourceFrame]) (by simp [sourceFrame])
      (ready_store a p coeff hc h)
  rw [he] at hn hys hrows
  have hflat : (SubexpNodeLiftData.nodeQuads p).flatMap flat =
      (SubexpMachineNodeOrder.nodeWords p).flatten := by
    rw [List.flatMap_def, SubexpFieldCacheInterpretation.nodeQuads_flat_encoded]
  have hz := RegisterResetProgram.all_eval
    (⟨SubexpFieldCacheLoad.resultRegs registers rf (saved a).regs,
      SubexpFieldCacheCall.resultStacks ports
        ((SubexpNodeLiftData.nodeQuads p).flatMap flat) (ys.flatMap flat)
        (SubexpFieldCacheNodeLoop.negativeBytes p 1 prepared.modulus
          (SubexpPreparedQuarticSetup.minusOne p 1) (SubexpNodeLiftData.nodeQuads p))
        (rows.flatten.flatMap flat) (saved a).stacks⟩ : Data)
  have hout : RegisterResetProgram.zeroed
    (⟨SubexpFieldCacheLoad.resultRegs registers rf (saved a).regs,
      SubexpFieldCacheCall.resultStacks ports
        ((SubexpNodeLiftData.nodeQuads p).flatMap flat) (ys.flatMap flat)
        (SubexpFieldCacheNodeLoop.negativeBytes p 1 prepared.modulus
          (SubexpPreparedQuarticSetup.minusOne p 1) (SubexpNodeLiftData.nodeQuads p))
        (rows.flatten.flatMap flat) (saved a).stacks⟩ : Data) = output a p ys rows := by
    simp only [RegisterResetProgram.zeroed, output, hflat, prepared,
      SubexpPreparedQuarticSetup.preparedData]
  rw [hout] at hz
  have hv : Values p ys rows := by
    constructor
    · exact List.Forall₂.imp
        (fun x y hxy => SubexpFieldCacheInterpretation.power_inverse_total p
          (a.stacks 139) hexp x y hxy) hys
    · apply List.Forall₂.imp ?_ hrows
      intro x row hrow
      have hrow' : List.Forall₂ (fun y inverse =>
          SubexpFieldCachePairLoop.PairValue p 1 (QuarticSearch.liftedCoefficients p 1)
            (a.stacks 139) x (SubexpQuarticNegMachine.negateWords p 1 prepared.modulus
              (SubexpPreparedQuarticSetup.minusOne p 1) y) inverse)
          (SubexpNodeLiftData.nodeQuads p) row := by
        simpa only [SubexpFieldCacheProgram.negativeWords, List.forall₂_map_left_iff] using hrow
      exact List.Forall₂.imp (fun y inverse hxy =>
        SubexpFieldCacheInterpretation.pair_inverse_total p prepared.modulus
          (SubexpPreparedQuarticSetup.minusOne p 1) (SubexpPreparedQuarticSetup.minusOne_value p 1)
          (a.stacks 139) hexp x y inverse hxy) hrow'
    · have hl := (SubexpFieldCacheProgram.output_lengths p 1 prepared.modulus
        (SubexpPreparedQuarticSetup.minusOne p 1) (QuarticSearch.liftedCoefficients p 1)
        (a.stacks 139) (SubexpNodeLiftData.nodeQuads p) ys rows hys hrows).1
      simpa only [SubexpFieldCacheInterpretation.nodeQuads_length] using hl
    · have hl := (SubexpFieldCacheProgram.output_lengths p 1 prepared.modulus
        (SubexpPreparedQuarticSetup.minusOne p 1) (QuarticSearch.liftedCoefficients p 1)
        (a.stacks 139) (SubexpNodeLiftData.nodeQuads p) ys rows hys hrows).2.2
      simpa only [SubexpFieldCacheInterpretation.nodeQuads_length] using hl
  refine ⟨6 * (a.stacks 14).length + 6 + (n + 16), ys, rows, ?_, hv,
    hs.seq (ht.seq hz)⟩
  rw [SubexpFieldCacheInterpretation.nodeQuads_length] at hn
  unfold runtimeBound
  omega

theorem program_runsIn (a : Data) (p : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (h : Ready a p coeff hc) (hexp : BinaryArithmetic.toNat (a.stacks 139) = p^4 - 2) :
    ∃ ys rows, Values p ys rows ∧ RunsIn program (runtimeBound a p)
      (a.withPC (some program.entry)) ((output a p ys rows).withPC none) := by
  obtain ⟨n, ys, rows, hn, hv, ht⟩ := command_value a p coeff hc h hexp
  exact ⟨ys, rows, hv, n + 1, hn, compiled_halt_trace ht 134 137⟩

theorem output_frame (a : Data) (p : ℕ) [Fact p.Prime]
    (ys : List (Quad (Word (baseWidth p 1))))
    (rows : List (List (Quad (Word (baseWidth p 1)))))
    (i : Fin 140) (h14 : i ≠ 14) (h134 : i ≠ 134) (h135 : i ≠ 135)
    (h136 : i ≠ 136) (h137 : i ≠ 137) (h138 : i ≠ 138) :
    (output a p ys rows).stacks i = a.stacks i := by
  change SubexpFieldCacheCall.resultStacks ports _ _ _ _ (saved a).stacks i = _
  rw [SubexpFieldCacheCall.resultStacks_frame ports _ _ _ _ _ i h134 h135 h136 h137]
  simp only [saved, Function.update_of_ne h138, Function.update_of_ne h14]

theorem runtimeBound_le (a : Data) (p W : ℕ)
    (hB : baseWidth p 1 ≤ W) (hL : (a.stacks 14).length ≤ W)
    (hE : (a.stacks 139).length ≤ W) (hN : BinaryArithmetic.toNat (a.stacks 139) ≤ W)
    (hQ : p^4 - 1 ≤ W) :
    runtimeBound a p ≤ SubexpFieldCacheProgram.polynomialBound W + 15 * W + 32 := by
  have hb := SubexpFieldCacheProgram.budget_le (baseWidth p 1) (a.stacks 139) (p^4 - 1)
    W hB hE hN hQ
  unfold runtimeBound
  omega

end SubexponentialSAT.SubexpMainFieldCacheCore

end OAI.Algorithms
