import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainRowPreparation
import OAI.Algorithms.SubexponentialSAT.SubexpSourceRowReady

namespace OAI.Algorithms

/-! The actual Main row preparation establishes the complete arithmetic
context of the row interpreter. Its logical context is reconstructed from
the resulting physical store, including the copied high traversal inputs.
No interpreter-ready state is supplied by the caller. -/

namespace SubexponentialSAT.SubexpMainRowContext

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)
open SubexpLiftRing SubexpQuarticRing
open SubexpRowPostfixInterpreter (contextStore physicalCfg ports)

attribute [local simp] Fin.coe_ofNat_eq_mod

noncomputable def input {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    SubexpSourceRowReady.Data :=
  SubexpMainRowSetup.projected alloc (SubexpMainRowPreparation.pre alloc a)

noncomputable def store {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    Fin 256 → List Bool := fun i =>
  (SubexpMainRowPreparation.result alloc a).stacks
    (ordinary alloc ⟨i.val, by omega⟩)

noncomputable def context {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    Fin 252 → List Bool := fun i => store alloc a (ports (Fin.natAdd 4 i))

theorem store_low {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 256) (hi : i.val < 250) :
    store alloc a i = (SubexpSourceRowContext.result (input alloc a)).stacks i :=
  SubexpMainRowPreparation.result_native alloc a i hi

theorem input_source {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 10) :
    (input alloc a).stacks ⟨128 + i.val, by omega⟩ =
      a.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) := by
  change (SubexpMainRowPreparation.pre alloc a).stacks
    ((SubexpMainRowSetup.contextProcedure er alloc).stack (⟨128 + i.val, by omega⟩ : Fin 256)) = _
  have hm : (SubexpMainRowSetup.contextProcedure er alloc).stack (⟨128 + i.val, by omega⟩ : Fin 256) =
      ordinary alloc ⟨128 + i.val, by omega⟩ := by
    change SubexpSourceRowContext.Main.stackMap (SubexpMainRowSetup.contextAllocation alloc)
      ⟨128 + i.val, by omega⟩ = _
    have hr : (⟨128 + i.val, by omega⟩ : Fin 256) ≠ SubexpSourceRowContext.radiusInput := by
      intro he
      have hv := congrArg (fun j : Fin 256 => j.val) he
      change 128 + i.val = 250 at hv
      omega
    have hw : (⟨128 + i.val, by omega⟩ : Fin 256) ≠ SubexpSourceRowContext.targetWidthInput := by
      intro he
      have hv := congrArg (fun j : Fin 256 => j.val) he
      change 128 + i.val = 251 at hv
      omega
    simp only [SubexpSourceRowContext.Main.stackMap, ite_eq_right hr, ite_eq_right hw, ordinary]
  rw [hm]
  exact SubexpMainRowPreclear.result_source alloc a i

theorem input_radius {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    (input alloc a).stacks SubexpSourceRowContext.radiusInput =
      a.stacks (persistent es 25) :=
  SubexpMainRowPreclear.result_persistent alloc a 25

theorem input_target_width {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    (input alloc a).stacks SubexpSourceRowContext.targetWidthInput =
      a.stacks (persistent es 13) :=
  SubexpMainRowPreclear.result_persistent alloc a 13

theorem store_interpreter_empty {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 4) : store alloc a (ports (i.castAdd 252)) = [] := by
  fin_cases i
  all_goals
    rw [store_low alloc a _ (by decide)]
    exact SubexpSourceRowContext.result_empty _ _ (by decide)
      (SubexpSourceRowContext.copies_avoid _ (by decide)) (by decide) (by decide) (by decide)

theorem contextStore_eq {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    contextStore (context alloc a) = store alloc a := by
  funext i
  obtain ⟨j, rfl⟩ := ports.surjective i
  refine Fin.addCases (m := 4) (n := 252) ?_ ?_ j
  · intro j
    rw [store_interpreter_empty]
    fin_cases j <;> rfl
  · intro j
    exact SubexpRowPostfixInterpreter.physicalCfg_context _ _ _ _ _ _ _ _ j

theorem context_below250 {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 256) (hi : i.val < 250) :
    contextStore (context alloc a) i =
      contextStore (SubexpSourceRowReady.context (input alloc a)) i := by
  rw [contextStore_eq, SubexpSourceRowReady.contextStore_eq_result]
  exact store_low alloc a i hi

/-- Actual copied source cache words establish the interpreter contract.
The dimension comes from the physical binary radius input. -/
theorem ready {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (p : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p 1)
    (t z : SubexpRowPolynomialCalls.Coefficient p 1)
    (hmodulus : a.stacks (ordinary alloc 128) = M.bits)
    (hreduction : a.stacks (ordinary alloc 130) = SubexpQuarticFlatMul.flat t)
    (hwidth : (a.stacks (ordinary alloc 129)).length = baseWidth p 1)
    (hzero : SubexpFlatAdd.encode z = List.replicate (4 * baseWidth p 1) false) :
    SubexpRowPostfixContext.Ready p 1 M t z
      (CounterPrograms.value (a.stacks (persistent es 25)) + 1)
      (a.stacks (ordinary alloc 129))
      (SubexpSourceRowReady.scalarFrame (input alloc a)) (context alloc a) := by
  have hM : (input alloc a).stacks 128 = M.bits :=
    (input_source alloc a 0).trans hmodulus
  have ht : (input alloc a).stacks 130 = SubexpQuarticFlatMul.flat t :=
    (input_source alloc a 2).trans hreduction
  have h129 : (input alloc a).stacks (129 : Fin 256) =
      a.stacks (ordinary alloc 129) := input_source alloc a 1
  have hw : ((input alloc a).stacks 129).length = baseWidth p 1 := by
    rw [h129]
    exact hwidth
  have H := SubexpSourceRowReady.ready p M t z (input alloc a) hM ht hw hzero
  have H' := SubexpSourceRowReady.ready_congr_below250 p 1 M t z _ _ _ _
    (context alloc a) H (context_below250 alloc a)
  simpa only [SubexpSourceRowContext.dimension, input_radius, h129] using H'

theorem target_width {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    contextStore (context alloc a) 74 = a.stacks (persistent es 13) := by
  rw [context_below250 alloc a 74 (by decide), SubexpSourceRowReady.target_width,
    input_target_width]

theorem output_empty {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    contextStore (context alloc a) 87 = [] := by
  rw [context_below250 alloc a 87 (by decide)]
  exact SubexpSourceRowReady.output_empty _

theorem source_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 10) : store alloc a ⟨128 + i.val, by omega⟩ =
      a.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) := by
  rw [store_low alloc a _ (by change 128 + i.val < 250; omega),
    SubexpSourceRowContext.result_source]
  exact input_source alloc a i

end SubexponentialSAT.SubexpMainRowContext

end OAI.Algorithms
