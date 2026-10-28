import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainFieldCachePorts
import OAI.Algorithms.SubexponentialSAT.SubexpMainFieldCacheExecution

namespace OAI.Algorithms

/-! The complete prepared-ring/node-to-cache phase in the Main ABI. -/

namespace SubexponentialSAT.SubexpMainFieldCache

open BitProgram StructuredCalls SubexpMainProgram
open BinaryArithmetic SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem output_slots (a : SubexpMainFieldCacheCore.Data) (p : ℕ) [Fact p.Prime]
    (ys : List (Quad (Word (baseWidth p 1))))
    (rows : List (List (Quad (Word (baseWidth p 1))))) :
    let out := SubexpMainFieldCacheCore.output a p ys rows
    out.stacks 134 = (SubexpMachineNodeOrder.nodeWords p).flatten ∧
    out.stacks 135 = ys.flatMap SubexpQuarticFlatMul.flat ∧
    out.stacks 136 = SubexpFieldCacheNodeLoop.negativeBytes p 1
      (SubexpPreparedQuarticSetup.modulus p 1) (SubexpPreparedQuarticSetup.minusOne p 1)
      (SubexpNodeLiftData.nodeQuads p) ∧
    out.stacks 137 = rows.flatten.flatMap SubexpQuarticFlatMul.flat ∧
    out.stacks 138 = a.stacks 14 ∧ out.stacks 14 = [] := by
  have h97 : SubexpMainFieldCacheCore.ports 97 = 134 := by decide
  have h98 : SubexpMainFieldCacheCore.ports 98 = 135 := by decide
  have h100 : SubexpMainFieldCacheCore.ports 100 = 136 := by decide
  have h103 : SubexpMainFieldCacheCore.ports 103 = 137 := by decide
  simp [SubexpMainFieldCacheCore.output, SubexpFieldCacheCall.resultStacks,
    h97, h98, h100, h103, SubexpMainFieldCacheCore.saved]

def runtimeBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) (p : ℕ) : ℕ :=
  SubexpMainFieldCacheCore.runtimeBound ((procedure er alloc).project a) p

structure Result {er es : ℕ} (alloc : Allocation es) (a b : MainState er es)
    (p D : ℕ) [Fact p.Prime] : Prop where
  arrays : ∃ (ys : List (Quad (Word (baseWidth p 1))))
      (rows : List (List (Quad (Word (baseWidth p 1))))),
    SubexpMainFieldCacheCore.Values p ys rows ∧
    b.stacks (ordinary alloc 134) = (SubexpMachineNodeOrder.nodeWords p).flatten ∧
    b.stacks (ordinary alloc 135) = ys.flatMap SubexpQuarticFlatMul.flat ∧
    b.stacks (ordinary alloc 136) = SubexpFieldCacheNodeLoop.negativeBytes p 1
      (SubexpPreparedQuarticSetup.modulus p 1) (SubexpPreparedQuarticSetup.minusOne p 1)
      (SubexpNodeLiftData.nodeQuads p) ∧
    b.stacks (ordinary alloc 137) = rows.flatten.flatMap SubexpQuarticFlatMul.flat
  saved : b.stacks (ordinary alloc 300) = a.stacks (ordinary alloc 14)
  lifted : b.stacks (ordinary alloc 300) = ProgramEncoding.encodeRecords
    (SubexpNodeLiftData.liftedNodeWords p (D + 1) (SubexpPreparedQuarticSetup.modulus p 1))
  scratch : ∀ i : Fin 110, b.stacks (ordinary alloc ⟨i.val, by omega⟩) = []
  frame : ∀ i, i ≠ ordinary alloc 14 → i ≠ ordinary alloc 134 →
    i ≠ ordinary alloc 135 → i ≠ ordinary alloc 136 → i ≠ ordinary alloc 137 →
    i ≠ ordinary alloc 300 → b.stacks i = a.stacks i
  registers : ∀ i : Fin 16, b.regs ((procedure er alloc).registerMap i) = false
  registerFrame : ∀ i, (¬ ∃ j, (procedure er alloc).registerMap j = i) →
    b.regs i = a.regs i
  controls : ∀ i, b.regs (controlRegister er i) = a.regs (controlRegister er i)

theorem install_result {er es : ℕ} (alloc : Allocation es) (d : MainState er es)
    (p D : ℕ) [Fact p.Prime] (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (hready : SubexpMainFieldCacheCore.Ready ((procedure er alloc).project d) p coeff hc)
    (hlifted : d.stacks (ordinary alloc 14) = ProgramEncoding.encodeRecords
      (SubexpNodeLiftData.liftedNodeWords p (D + 1) (SubexpPreparedQuarticSetup.modulus p 1)))
    (ys : List (Quad (Word (baseWidth p 1))))
    (rows : List (List (Quad (Word (baseWidth p 1)))))
    (hv : SubexpMainFieldCacheCore.Values p ys rows) :
    Result alloc d ((procedure er alloc).install d
      (SubexpMainFieldCacheCore.output ((procedure er alloc).project d) p ys rows)) p D := by
  let out := SubexpMainFieldCacheCore.output ((procedure er alloc).project d) p ys rows
  have hs (i : Fin 140) : ((procedure er alloc).install d out).stacks (stackMap alloc i) =
      out.stacks i := embedState_stack (procedure er alloc).registerMap
        (procedure er alloc).stack d out (procedure er alloc).stack.injective i
  have ho (i : Fin 140) := SubexpMainFieldCacheCore.output_frame
    ((procedure er alloc).project d) p ys rows i
  have hslots := output_slots ((procedure er alloc).project d) p ys rows
  constructor
  · refine ⟨ys, rows, hv, ?_, ?_, ?_, ?_⟩
    · exact (hs 134).trans hslots.1
    · exact (hs 135).trans hslots.2.1
    · exact (hs 136).trans hslots.2.2.1
    · exact (hs 137).trans hslots.2.2.2.1
  · exact (hs 138).trans hslots.2.2.2.2.1
  · exact (hs 138).trans (hslots.2.2.2.2.1.trans hlifted)
  · intro i
    let j : Fin 140 := ⟨i.val, by omega⟩
    have hj : stackMap alloc j = ordinary alloc ⟨i.val, by omega⟩ := by
      simp only [stackMap, j, dite_eq_left (show i.val < 138 by omega)]
    have hh := hs j
    change ((procedure er alloc).install d out).stacks (stackMap alloc j) = out.stacks j at hh
    rw [hj] at hh
    apply hh.trans
    by_cases hi : j = 14
    · rw [hi]; exact hslots.2.2.2.2.2
    · rw [ho j hi (by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega)
        (by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega)
        (by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega)
        (by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega)
        (by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega)]
      exact hready.empty j (Or.inl ⟨i.isLt, hi⟩)
  · intro i h14 h134 h135 h136 h137 h300
    by_cases hm : ∃ j, stackMap alloc j = i
    · obtain ⟨j, rfl⟩ := hm
      exact (hs j).trans (ho j
        (by intro h; subst j; exact h14 rfl)
        (by intro h; subst j; exact h134 rfl)
        (by intro h; subst j; exact h135 rfl)
        (by intro h; subst j; exact h136 rfl)
        (by intro h; subst j; exact h137 rfl)
        (by intro h; subst j; exact h300 rfl))
    · exact embedState_stack_frame _ _ _ _ _ hm
  · intro i
    exact (embedState_register _ _ _ _ (procedure er alloc).registerMap_injective i).trans rfl
  · intro i hi
    exact embedState_register_frame _ _ _ _ _ hi
  · exact Procedure.install_control _ _ _

/-- The cache consumes the concrete outputs of the two earlier Main phases.
Only previously unused workspace must initially be empty; cache readiness,
selected coefficients, node order, and physical prepared words are derived. -/
theorem execution {er es : ℕ} (alloc : Allocation es)
    (a b d : MainState er es) (p D : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (hp : SubexpMainPreparedRings.Result (ringAllocation alloc) a b p D coeff hc)
    (hn : SubexpMainFieldNodes.Result (nodeAllocation alloc) b d p (D + 1)
      (SubexpPreparedQuarticSetup.modulus p 1))
    (he : ∀ i, initiallyEmpty i → a.stacks (ordinary alloc i) = [])
    (hexp : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p^4 - 2) :
    ∃ n ≤ runtimeBound alloc d p, ∃ e,
      Eval (procedure er alloc).invoke n d e ∧ Result alloc d e p D := by
  have hready := ready_from_phases alloc a b d p D coeff hc hp hn he
  have hexp' : BinaryArithmetic.toNat (d.stacks (persistent es 29)) = p^4 - 2 := by
    rw [hn.persistent_frame 29, hp.persistent_frame 29 (by decide)]
    exact hexp
  obtain ⟨ys, rows, hv, n, hn', ht⟩ := SubexpMainFieldCacheCore.program_runsIn
    ((procedure er alloc).project d) p coeff hc hready hexp'
  exact ⟨n, hn', (procedure er alloc).install d
    (SubexpMainFieldCacheCore.output ((procedure er alloc).project d) p ys rows),
    Procedure.invoke_trace _ _ _ ht, install_result alloc d p D coeff hc hready hn.lifted ys rows hv⟩

theorem program_runsIn {er es : ℕ} (alloc : Allocation es)
    (a b d : MainState er es) (p D : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (hp : SubexpMainPreparedRings.Result (ringAllocation alloc) a b p D coeff hc)
    (hn : SubexpMainFieldNodes.Result (nodeAllocation alloc) b d p (D + 1)
      (SubexpPreparedQuarticSetup.modulus p 1))
    (he : ∀ i, initiallyEmpty i → a.stacks (ordinary alloc i) = [])
    (hexp : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p^4 - 2) :
    ∃ e, RunsIn (program er alloc) (runtimeBound alloc d p)
      (d.withPC (some (program er alloc).entry)) (e.withPC none) ∧ Result alloc d e p D := by
  obtain ⟨n, hbound, e, ht, hr⟩ := execution alloc a b d p D coeff hc hp hn he hexp
  refine ⟨e, ⟨n, hbound, ?_⟩, hr⟩
  cases ht with
  | call _ htrace => exact htrace

theorem primitive_execution {er es : ℕ} (alloc : Allocation es)
    (a b d : MainState er es) (p D : ℕ) [Fact p.Prime]
    (coeff : Quad (Word (baseWidth p 1)))
    (hc : coeff.map (SubexpWordLift.sourceValue p) = Quad.ofFn (QuarticSearch.coefficients p))
    (hp : SubexpMainPreparedRings.Result (ringAllocation alloc) a b p D coeff hc)
    (hn : SubexpMainFieldNodes.Result (nodeAllocation alloc) b d p (D + 1)
      (SubexpPreparedQuarticSetup.modulus p 1))
    (he : ∀ i, initiallyEmpty i → a.stacks (ordinary alloc i) = [])
    (hexp : BinaryArithmetic.toNat (a.stacks (persistent es 29)) = p^4 - 2) :
    ∃ e, Computation.RunsIn (primitive (program er alloc)).step
      (primitiveOverhead (program er alloc) * runtimeBound alloc d p)
      (primitiveCfg (program er alloc) (d.withPC (some (program er alloc).entry)))
      (primitiveCfg (program er alloc) (e.withPC none)) ∧ Result alloc d e p D := by
  obtain ⟨e, ht, hr⟩ := program_runsIn alloc a b d p D coeff hc hp hn he hexp
  exact ⟨e, BitProgram.primitive_execution _ ht, hr⟩

theorem runtimeBound_le {er es : ℕ} (alloc : Allocation es) (d : MainState er es)
    (p W : ℕ) (hB : baseWidth p 1 ≤ W)
    (hL : (d.stacks (ordinary alloc 14)).length ≤ W)
    (hE : (d.stacks (persistent es 29)).length ≤ W)
    (hN : BinaryArithmetic.toNat (d.stacks (persistent es 29)) ≤ W) (hQ : p^4 - 1 ≤ W) :
    runtimeBound alloc d p ≤ SubexpFieldCacheProgram.polynomialBound W + 15 * W + 32 :=
  SubexpMainFieldCacheCore.runtimeBound_le ((procedure er alloc).project d) p W
    hB hL hE hN hQ

theorem Result.persistent_frame {er es : ℕ} {alloc : Allocation es}
    {a b : MainState er es} {p D : ℕ} [Fact p.Prime]
    (h : Result alloc a b p D) (i : Fin 32) :
    b.stacks (persistent es i) = a.stacks (persistent es i) := by
  have hw := alloc.enough.trans alloc.within
  apply h.frame <;> intro he <;> have hv := congrArg Fin.val he <;>
    simp only [persistent, Fin.val_natAdd, ordinary] at hv <;> omega

theorem Result.sourceCache_frame {er es : ℕ} {alloc : Allocation es}
    {a b : MainState er es} {p D : ℕ} [Fact p.Prime]
    (h : Result alloc a b p D) (i : Fin 6) :
    b.stacks (SubexpMainPreparedRings.sourcePort (ringAllocation alloc) i) =
      a.stacks (SubexpMainPreparedRings.sourcePort (ringAllocation alloc) i) := by
  apply h.frame <;> intro he <;> have hv := congrArg Fin.val he <;>
    simp only [SubexpMainPreparedRings.sourcePort, ordinary] at hv <;> omega

theorem Result.cache_lengths {er es : ℕ} {alloc : Allocation es}
    {a b : MainState er es} {p D : ℕ} [Fact p.Prime]
    (h : Result alloc a b p D) :
    (b.stacks (ordinary alloc 134)).length = 4 * baseWidth p 1 * (p^4 - 1) ∧
    (b.stacks (ordinary alloc 135)).length = 4 * baseWidth p 1 * (p^4 - 1) ∧
    (b.stacks (ordinary alloc 136)).length = 4 * baseWidth p 1 * (p^4 - 1) ∧
    (b.stacks (ordinary alloc 137)).length = 4 * baseWidth p 1 * (p^4 - 1) * (p^4 - 1) := by
  obtain ⟨ys, rows, hv, h134, h135, h136, h137⟩ := h.arrays
  rw [h134, h135, h136, h137]
  refine ⟨?_, hv.inverse_length, ?_, hv.difference_length⟩
  · rw [← SubexpFieldCacheInterpretation.nodeQuads_flat_encoded,
      ← List.flatMap_def, SubexpFieldCacheNodeLoop.flatMap_length,
      SubexpFieldCacheInterpretation.nodeQuads_length]
  · rw [SubexpFieldCacheNodeLoop.negativeBytes_length,
      SubexpFieldCacheInterpretation.nodeQuads_length]

end SubexponentialSAT.SubexpMainFieldCache

end OAI.Algorithms
