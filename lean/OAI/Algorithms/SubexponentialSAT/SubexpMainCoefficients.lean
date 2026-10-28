import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCoefficientProgram
import OAI.Algorithms.SubexponentialSAT.SubexpMainCoefficientPorts

namespace OAI.Algorithms

/-! Actual Main coefficient generation, including interval initialization.
The source parameters remain in their persistent ports. The executed local
program makes its own work copies, computes A, normalizes p, converts A/R,
searches, and physically duplicates the resulting coefficient stream. -/

namespace SubexponentialSAT.SubexpMainCoefficients

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupStorage
open SubexpLayoutPorts Subexp

def procedure (er : ℕ) {es : ℕ} (a : Allocation es) : Procedure er es where
  registers := 16
  stackCount := 64
  labels := size SubexpCoefficientProgram.command + 1
  program := SubexpCoefficientProgram.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin (workRegs er) => x.val) h)⟩
  stack := ⟨stackMap a, stackMap_injective a⟩

theorem stackMap_retained_high {es : ℕ} (a : Allocation es) (i : Fin 64)
    (hi : SubexpCoefficientProgram.retained i) : 64 ≤ (stackMap a i).val := by
  have hw := a.enough.trans a.within
  rcases hi with hi | hi | hi
  · have hc : i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 := by
      simp only [Fin.ext_iff, Fin.coe_ofNat_eq_mod]
      omega
    rcases hc with rfl | rfl | rfl | rfl <;>
      simp [stackMap, persistent] <;> omega
  · subst i
    change 64 ≤ 649
    decide
  · subst i
    change 64 ≤ 254
    decide

theorem stackMap_high_input {es : ℕ} (a : Allocation es) (i : Fin 64)
    (hi : 64 ≤ (stackMap a i).val)
    (hc : stackMap a i ≠ master a 9) (hl : stackMap a i ≠ ordinary a 254) :
    40 ≤ i.val ∧ i.val ≤ 43 := by
  by_cases h40 : i = 40
  · subst i; decide
  by_cases h41 : i = 41
  · subst i; decide
  by_cases h42 : i = 42
  · subst i; decide
  by_cases h43 : i = 43
  · subst i; decide
  by_cases h48 : i = 48
  · subst i; exact (hc rfl).elim
  by_cases h49 : i = 49
  · subst i; exact (hl rfl).elim
  have hi' : 64 ≤ i.val := by
    simpa only [stackMap, ite_eq_right h40, ite_eq_right h41, ite_eq_right h42, ite_eq_right h43,
      ite_eq_right h48, ite_eq_right h49, low, ordinary, Fin.val_castLE] using hi
  omega

structure Result {er es : ℕ} (alloc : Allocation es) (a b : MainState er es)
    (p r Q R : ℕ) [Fact p.Prime] where
  coefficients : Fin R → ZMod p
  output : b.stacks (master alloc 9) = CoefficientSearchSemantics.encode p coefficients
  duplicate : b.stacks (ordinary alloc 254) = b.stacks (master alloc 9)
  correct : CoefficientNormalization.unnormalize (List.ofFn coefficients) =
    CoefficientSearch.coefficientsNat p (TailInterval.intervalStart r Q R) R
  frame : ∀ i : Fin (totalStacks es), 64 ≤ i.val →
    i ≠ master alloc 9 → i ≠ ordinary alloc 254 → b.stacks i = a.stacks i
  scratch : ∀ i : Fin 64, b.stacks (low alloc i) = []
  registers : ∀ i : Fin 16, b.regs ((procedure er alloc).registerMap i) = false
  registerFrame : ∀ i, (¬ ∃ j, (procedure er alloc).registerMap j = i) → b.regs i = a.regs i
  control : ∀ i, b.regs (controlRegister er i) = a.regs (controlRegister er i)

theorem install_result {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (out : SubexpCoefficientStaging.Data) (p r Q R : ℕ) [Fact p.Prime]
    (ha : ∀ i : Fin 64, a.stacks (low alloc i) = [])
    (h : SubexpCoefficientProgram.Result ((procedure er alloc).project a) out p r Q R) :
    Nonempty (Result alloc a ((procedure er alloc).install a out) p r Q R) := by
  have hs (i : Fin 64) := embedState_stack (procedure er alloc).registerMap
    (procedure er alloc).stack a out (procedure er alloc).stack.injective i
  refine ⟨⟨h.coefficients, ?_, ?_, h.correct, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (hs 48).trans h.output
  · exact (hs 49).trans (h.duplicate.trans (hs 48).symm)
  · intro i hi hc hl
    by_cases hm : ∃ j, stackMap alloc j = i
    · obtain ⟨j, rfl⟩ := hm
      have hj := stackMap_high_input alloc j hi hc hl
      exact (hs j).trans (h.inputs j hj.1 hj.2)
    · exact embedState_stack_frame _ _ a out i hm
  · intro i
    by_cases hm : ∃ j, stackMap alloc j = low alloc i
    · obtain ⟨j, hj⟩ := hm
      have hnot : ¬ SubexpCoefficientProgram.retained j := by
        intro hret
        have hh := stackMap_retained_high alloc j hret
        rw [hj] at hh
        change 64 ≤ i.val at hh
        omega
      rw [← hj]
      exact (hs j).trans (h.empty j hnot)
    · exact (embedState_stack_frame _ _ a out (low alloc i) hm).trans (ha i)
  · intro i
    exact (embedState_register _ _ a out (procedure er alloc).registerMap_injective i).trans
      (h.registers i)
  · intro i hi
    exact embedState_register_frame _ _ a out i hi
  · intro i
    exact Procedure.install_control _ _ _ i

theorem invoke_run {er es : ℕ} (alloc : Allocation es) (p r Q R B : ℕ) [Fact p.Prime]
    (hr : 0 < r) (h2 : (2 : ZMod p) ≠ 0) (a : MainState er es)
    (ha : WordBound B a) (hempty : ∀ i : Fin 64, a.stacks (low alloc i) = [])
    (hpw : CounterPrograms.value (a.stacks (persistent es 6)) = p)
    (hrw : CounterPrograms.value (a.stacks (persistent es 21)) = r)
    (hQw : CounterPrograms.value (a.stacks (persistent es 17)) = Q)
    (hRw : CounterPrograms.value (a.stacks (persistent es 25)) = R) :
    ∃ t b, Eval (procedure er alloc).invoke t a b ∧
      t ≤ SubexpCoefficientProgram.budget p r Q R B ∧
      Nonempty (Result alloc a b p r Q R) := by
  have hlocal : WordBound B ((procedure er alloc).project a) :=
    fun i => ha ((procedure er alloc).stack i)
  obtain ⟨out, ht, hw, hres⟩ := SubexpCoefficientProgram.program_run p r Q R B hr h2
    ((procedure er alloc).project a) hlocal hpw hrw hQw hRw
  obtain ⟨t, htime, htrace⟩ := ht
  refine ⟨t, (procedure er alloc).install a out,
    (procedure er alloc).invoke_trace a out htrace, htime, ?_⟩
  exact install_result alloc a out p r Q R hempty hres.some

theorem Result.persistent_frame {er es : ℕ} {alloc : Allocation es}
    {a b : MainState er es} {p r Q R : ℕ} [Fact p.Prime]
    (h : Result alloc a b p r Q R) (i : Fin 32) :
    b.stacks (persistent es i) = a.stacks (persistent es i) := by
  have hw := alloc.enough.trans alloc.within
  apply h.frame
  · simp only [persistent, Fin.val_natAdd]
    omega
  · exact (master_ne_persistent alloc 9 i).symm
  · intro he
    have hv := congrArg (fun x : Fin (totalStacks es) => x.val) he
    simp only [persistent, Fin.val_natAdd, ordinary] at hv
    omega

end SubexponentialSAT.SubexpMainCoefficients

end OAI.Algorithms
