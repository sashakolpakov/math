import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLagrangeCacheControl

namespace OAI.Algorithms

/-! The cache's outer record order is restored by a charged physical pass. -/

namespace SubexponentialSAT.SubexpLagrangeCacheReverse

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLagrangeCacheControl

theorem reverse_run (s : Store) (cache : List (List (List Bool)))
    (hcache : s 250 = Subexp.FactorPacketCoordinates.cacheBytes cache)
    (h236 : s 236 = []) (h237 : s 237 = []) (h238 : s 238 = []) (h245 : s 245 = []) :
    ExecutesIn reverseCache
      (10 * (Subexp.FactorPacketCoordinates.cacheBytes cache).length +
        6 * (Subexp.FactorPacketCoordinates.cacheBytes cache.reverse).length + 8)
      s (Function.update s 250 (Subexp.FactorPacketCoordinates.cacheBytes cache.reverse)) := by
  intro regs
  let a : SubexpLagrangeCacheControl.Data := ⟨regs, s⟩
  let b := Subexp.TupleProgram.pushedState 237 0 false a
  let records := cache.map (Encoding.encodeList id)
  have hpush := Subexp.TupleProgram.pushConst_eval 237 0 false a
  have hnative : projectState threeRegisters reversePorts b =
      SubexpNormalizeProgram.filterState (b.regs 0) (b.regs 1) (b.regs 2)
        (Encoding.encodeList id records ++ []) [] (Encoding.encodeList id []) [] := by
    apply SubexpScanPrimitives.state_ext
    · funext i
      fin_cases i <;> rfl
    · funext i
      fin_cases i <;>
        simp [projectState, reversePorts, b, a,
          SubexpNormalizeProgram.filterState, SubexpPostfixControl.quadruple,
          records, hcache, h236, h237, h238,
          Subexp.FactorPacketCoordinates.cacheBytes, ProgramEncoding.encodeRecords]
      rfl
  obtain ⟨n, hn, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn records [] [] []
    (b.regs 0) (b.regs 1) (b.regs 2)
  rw [← hnative] at ht
  have he := eval_call_from_state SubexpNormalizeProgram.reverseRecordsProgram
    threeRegisters reversePorts b threeRegisters.injective reversePorts.injective ht
  let small := SubexpNormalizeProgram.filterState false true false [] []
    (Encoding.encodeList id (records.reverse ++ [])) []
  let rf := Function.extend threeRegisters small.regs b.regs
  let mid := Function.update (Function.update s 250 []) 237
    (Subexp.FactorPacketCoordinates.cacheBytes cache.reverse)
  have hm : embedState threeRegisters reversePorts b small =
      (⟨rf, mid⟩ : SubexpLagrangeCacheControl.Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ threeRegisters.injective reversePorts.injective
    · intro i
      exact threeRegisters.injective.extend_apply _ _ i
    · intro i hi
      exact Function.extend_apply' _ _ _ hi
    · intro i
      fin_cases i <;> simp [mid, small, reversePorts, SubexpNormalizeProgram.filterState,
        SubexpPostfixControl.quadruple, h236, h238, records,
        Subexp.FactorPacketCoordinates.cacheBytes, ProgramEncoding.encodeRecords, List.map_reverse]
    · intro i hi
      have h250 : i ≠ 250 := fun h => hi ⟨0, h.symm⟩
      have h237' : i ≠ 237 := fun h => hi ⟨2, h.symm⟩
      simp [mid, b, a, h250, h237']
  change Eval _ n b (embedState threeRegisters reversePorts b small) at he
  rw [hm] at he
  have hmove := SubexpPolynomialConstructor.move_run mid 237 250
    (by decide) (by decide) (by decide) (by simp [mid, h245]) (by simp [mid]) rf
  obtain ⟨nm, rm, hnm, hmov⟩ := hmove
  have hout : Function.update (Function.update mid 237 []) 250 (mid 237) =
      Function.update s 250 (Subexp.FactorPacketCoordinates.cacheBytes cache.reverse) := by
    funext i
    by_cases hi : i = 237
    · subst i; simp [mid, h237]
    · by_cases hj : i = 250
      · subst i; simp [mid]
      · simp [mid, hi, hj]
  rw [hout] at hmov
  refine ⟨2 + (n + nm), rm, ?_, hpush.seq (he.seq hmov)⟩
  change n ≤ 10 * (Subexp.FactorPacketCoordinates.cacheBytes cache).length at hn
  simp only [mid, Function.update_self] at hnm
  omega

end SubexponentialSAT.SubexpLagrangeCacheReverse

end OAI.Algorithms
