import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPrefixControl

namespace OAI.Algorithms

/-! Actual primitive calls used by the factor-prefix grouping loops. -/

namespace SubexponentialSAT.SubexpFactorPrefixProgram

open BitProgram StructuredCalls
open Subexp.FactorPacketCoordinates (Word Prefix originBytes taylorBytes prefixBytes)
open Subexp.FactorPacketRows (prefixStream)

attribute [local simp] Fin.coe_ofNat_eq_mod

theorem pop_eval (src : Fin 24) (value present : Fin 8) (d : Data) :
    Eval (atom (.pop src value present)) 1 d
      ⟨readRegs d.regs value present (d.stacks src).head?,
        Function.update d.stacks src (d.stacks src).tail⟩ := by
  have h : (StructuredProgram.Atom.pop src value present).eval d =
      (⟨readRegs d.regs value present (d.stacks src).head?,
        Function.update d.stacks src (d.stacks src).tail⟩ : Data) := by
    cases hs : d.stacks src <;>
      simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg, execInstr, hs]
  rw [← h]
  exact .base (.atom _ _)

theorem push_eval (dst : Fin 24) (b : Bool) (d : Data) :
    Eval (push dst b) 2 d
      ⟨Function.update d.regs 0 b, Function.update d.stacks dst (b :: d.stacks dst)⟩ :=
  Subexp.TupleProgram.pushConst_eval dst 0 b d

theorem clear_eval (src : Fin 24) (d : Data) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d
      ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩ :=
  Subexp.TupleProgram.clear_eval src 0 1 d

theorem copy_eval (src dst : Fin 24) (hsd : src ≠ dst) (hst : src ≠ 17)
    (htd : (17 : Fin 24) ≠ dst) (d : Data) (ht : d.stacks 17 = []) :
    ∃ e, Eval (copy src dst) (7 * (d.stacks src).length + 5) d e ∧
      e.stacks = StackRoutines.copyStacks src dst d.stacks :=
  Subexp.MatrixProgramSupport.copy_eval src dst 17 hsd hst htd d ht

theorem readWord_eval (src dst : Fin 24) (hsd : src ≠ dst) (hst : src ≠ 16)
    (htd : (16 : Fin 24) ≠ dst) (d : Data) (bits tail : Word)
    (hs : d.stacks src = Encoding.frame bits ++ tail)
    (hd : d.stacks dst = []) (ht : d.stacks 16 = []) :
    ∃ e, Eval (readWord src dst hst) (9 * bits.length + 7) d e ∧
      e.stacks = Function.update (Function.update d.stacks src tail) dst bits :=
  Subexp.MatrixProgramSupport.readWord_eval src dst 16 hsd hst htd d bits tail hs hd ht

theorem emitFrame_eval (src dst : Fin 24) (hsd : src ≠ dst) (hst : src ≠ 16)
    (htd : (16 : Fin 24) ≠ dst) (d : Data) (ht : d.stacks 16 = []) :
    ∃ e, Eval (emitFrame src dst htd) (8 * (d.stacks src).length + 8) d e ∧
      e.stacks = Function.update (Function.update d.stacks src []) dst
        (Encoding.frame (d.stacks src) ++ d.stacks dst) :=
  Subexp.MatrixProgramSupport.emitFrame_eval src dst 16 hsd hst htd d ht

theorem readRecord_eval (src dst : Fin 24) (hsd : src ≠ dst) (hst : src ≠ 16)
    (htd : (16 : Fin 24) ≠ dst) (d : Data) (bits tail : Word)
    (hs : d.stacks src = true :: (Encoding.frame bits ++ tail))
    (hd : d.stacks dst = []) (ht : d.stacks 16 = []) :
    ∃ e, Eval (.seq (atom (.pop src 0 1)) (readWord src dst hst))
      (9 * bits.length + 8) d e ∧
      e.stacks = Function.update (Function.update d.stacks src tail) dst bits := by
  let a : Data := ⟨readRegs d.regs 0 1 (some true),
    Function.update d.stacks src (Encoding.frame bits ++ tail)⟩
  have hp : Eval (atom (.pop src 0 1)) 1 d a := by
    simpa only [hs, List.head?_cons, List.tail_cons] using pop_eval src 0 1 d
  obtain ⟨e, he, heq⟩ := readWord_eval src dst hsd hst htd a bits tail
    (by simp [a]) (by simp [a, hsd.symm, hd]) (by simp [a, hst.symm, ht])
  refine ⟨e, ?_, ?_⟩
  · convert hp.seq he using 1
    omega
  · simpa only [a, Function.update_idem] using heq

theorem emitRecord_eval (src dst : Fin 24) (hsd : src ≠ dst) (hst : src ≠ 16)
    (htd : (16 : Fin 24) ≠ dst) (d : Data) (ht : d.stacks 16 = []) :
    ∃ e, Eval (emitRecord src dst htd) (8 * (d.stacks src).length + 10) d e ∧
      e.stacks = Function.update (Function.update d.stacks src []) dst
        (true :: (Encoding.frame (d.stacks src) ++ d.stacks dst)) := by
  obtain ⟨e, he, hs⟩ := emitFrame_eval src dst hsd hst htd d ht
  let f : Data := ⟨Function.update e.regs 0 true,
    Function.update e.stacks dst (true :: e.stacks dst)⟩
  have hp : Eval (push dst true) 2 e f := push_eval dst true e
  refine ⟨f, ?_, ?_⟩
  · simpa only [emitRecord, Nat.add_assoc] using he.seq hp
  · dsimp [f]
    rw [hs]
    simp only [Function.update_same, Function.update_idem]

theorem countScope_eval (records : List Word) (d : Data)
    (hi : d.stacks 6 = Encoding.encodeList id records) (ho : d.stacks 7 = []) :
    ∃ e, Eval countScope (SubexpSunflowerProgram.CountRecords.loopSteps records) d e ∧
      e.stacks = Function.update (Function.update d.stacks 6 []) 7
        (List.replicate records.length true) := by
  let a := SubexpScopeCountSetup.counterState (d.regs 0) (d.regs 1)
    (Encoding.encodeList id records) []
  let b := SubexpScopeCountSetup.counterState false false [] (List.replicate records.length true)
  have ha : a = projectState countRegisters countStacks d := by
    apply SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;>
        simp [a, SubexpScopeCountSetup.counterState, projectState, countStacks,
          ParserProgram.pair, hi, ho]
  have ht := SubexpScopeCountSetup.counter_trace records (d.regs 0) (d.regs 1)
  change Trace SubexpScopeCountSetup.counterProgram _ (a.withPC _) (b.withPC _) at ht
  rw [ha] at ht
  have he := eval_call_from_state SubexpScopeCountSetup.counterProgram countRegisters countStacks d
    countRegisters_injective countStacks_injective ht
  let e := embedState countRegisters countStacks d b
  refine ⟨e, he, ?_⟩
  funext i
  by_cases h6 : i = 6
  · subst i
    simpa [e, b, SubexpScopeCountSetup.counterState, countStacks, ParserProgram.pair] using
      embedState_stack countRegisters countStacks d b countStacks_injective 0
  by_cases h7 : i = 7
  · subst i
    simpa [e, b, SubexpScopeCountSetup.counterState, countStacks, ParserProgram.pair] using
      embedState_stack countRegisters countStacks d b countStacks_injective 1
  · rw [embedState_stack_frame countRegisters countStacks d b i (by
      rintro ⟨j, hj⟩
      fin_cases j <;> simp [countStacks] at hj <;> simp_all)]
    simp [h6, h7]

theorem reverseAt_eval (ports : Fin 4 ↪ Fin 24) (d : Data) (records acc : List Word)
    (h0 : d.stacks (ports 0) = Encoding.encodeList id records)
    (h2 : d.stacks (ports 2) = Encoding.encodeList id acc) (h3 : d.stacks (ports 3) = []) :
    ∃ n ≤ 10 * (Encoding.encodeList id records).length, ∃ e,
      Eval (reverseAt ports) n d e ∧
      e.stacks = Function.update (Function.update d.stacks (ports 0) []) (ports 2)
        (Encoding.encodeList id (records.reverse ++ acc)) := by
  let a := SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
    (Encoding.encodeList id records) (d.stacks (ports 1)) (Encoding.encodeList id acc) []
  let b := SubexpNormalizeProgram.filterState false true false [] (d.stacks (ports 1))
    (Encoding.encodeList id (records.reverse ++ acc)) []
  have ha : a = projectState reverseRegisters ports d := by
    apply SubexpScanPrimitives.state_ext
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;>
        simp [a, SubexpNormalizeProgram.filterState, SubexpPostfixControl.quadruple,
          projectState, h0, h2, h3]
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records acc []
    (d.stacks (ports 1)) (d.regs 0) (d.regs 1) (d.regs 2)
  simp only [List.append_nil] at ht
  change Trace SubexpNormalizeProgram.reverseRecordsProgram _ (a.withPC _) (b.withPC _) at ht
  rw [ha] at ht
  have he := eval_call_from_state SubexpNormalizeProgram.reverseRecordsProgram reverseRegisters ports d
    reverseRegisters_injective ports.injective ht
  let e := embedState reverseRegisters ports d b
  refine ⟨n, hn, e, he, ?_⟩
  funext i
  by_cases hin : ∃ j, ports j = i
  · obtain ⟨j, rfl⟩ := hin
    have hport := embedState_stack reverseRegisters ports d b ports.injective j
    rw [hport]
    fin_cases j <;>
      simp [b, SubexpNormalizeProgram.filterState, SubexpPostfixControl.quadruple,
        ports.injective.eq_iff, h3]
  · rw [embedState_stack_frame reverseRegisters ports d b i hin]
    have hnot0 : i ≠ ports 0 := fun h => hin ⟨0, h.symm⟩
    have hnot2 : i ≠ ports 2 := fun h => hin ⟨2, h.symm⟩
    simp [hnot0, hnot2]

end SubexponentialSAT.SubexpFactorPrefixProgram

end OAI.Algorithms
