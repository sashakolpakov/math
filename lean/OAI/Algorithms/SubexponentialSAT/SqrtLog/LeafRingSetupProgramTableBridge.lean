import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramBase

namespace OAI.Algorithms

/-! Physical table-input projection and the exact native table-call bridge. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing RingProgramTable

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Physical inputs to the table producer. The polynomial bytes are supplied
by `searchAndPad_eval`, and the scalar bytes by `scalarCall_eval`. -/
structure TableInput (t d : ℕ) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (a : LeafRingSetupProgram.Data) : Prop where
  modulus : a.stacks 194=M.bits
  width : (a.stacks 202).length=baseWidth 3 t
  degree : (a.stacks 204).length=d
  seed : a.stacks 538=cache.one.val
  zero : a.stacks 203=cache.zero.val
  minusOne : a.stacks 508=cache.minusOne.val
  coefficients : a.stacks 441=wordBits (modelCoefficients t model).val
  clean : ∀ i : Fin 42, i ∉ ([0,5,12,17,21,22,24] : List (Fin 42)) →
    a.stacks (LeafRingSetupProgram.table i)=[]

def tableInputStore (a : LeafRingSetupProgram.Data) : Store where
  modulus := a.stacks 194
  width := a.stacks 202
  minusOne := a.stacks 508
  tail := []
  polynomial := a.stacks 441
  degree := a.stacks 204
  zero := a.stacks 203

theorem TableInput.project {t d : ℕ} {model : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {a : LeafRingSetupProgram.Data} (h : TableInput t d model M cache a) :
    projectState (registers 8 (by decide)) LeafRingSetupProgram.table a =
      Machine.state (a.regs ∘ registers 8 (by decide))
        (initialStore (tableInputStore a) (modelCoefficients t model)
          cache.one cache.zero cache.minusOne) [] := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  have hc := h.clean i
  fin_cases i <;>
    simp [LeafRingSetupProgram.table,tapes,initialStore,
      tableInputStore,h.seed,h.zero,h.minusOne,h.coefficients] at hc ⊢
  all_goals exact hc

/-- No table is supplied to this call. It runs native power recurrence and
layout on the actual runtime coefficient array. -/
theorem tableCall_produces (t : ℕ) {d : ℕ} (hd : 0 < d) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (ho : BinaryArithmetic.toNat cache.one.val < 3^t)
    (a : LeafRingSetupProgram.Data) (h : TableInput t d model M cache a) :
    ∃ n ≤ 208000*(d+1)^5*(t+1)^2, ∃ e : LeafRingSetupProgram.Data,
      Eval tableCall n a e ∧ e.stacks 201=modelTable t model M cache ∧
      e.stacks 194=a.stacks 194 ∧ e.stacks 202=a.stacks 202 ∧
      e.stacks 203=cache.zero.val ∧ e.stacks 204=a.stacks 204 ∧
      e.stacks 508=cache.minusOne.val ∧
      (∀ i, (¬ ∃ j, LeafRingSetupProgram.table j=i) → e.stacks i=a.stacks i) := by
  obtain ⟨rf,n,hn,he⟩ := table_program_run t hd model M cache hz ho
    (tableInputStore a) (a.regs ∘ registers 8 (by decide)) h.modulus h.width h.degree
  let out := Machine.state rf
    (preparedStore 3 t M cache (modelCoefficients t model) (tableInputStore a))
    (modelTable t model M cache)
  let e := embedState (registers 8 (by decide)) LeafRingSetupProgram.table a out
  have he' : Eval tableCall n a e :=
    eval_call_from_state Machine.program (registers 8 (by decide)) LeafRingSetupProgram.table
      a (registers_injective 8 (by decide)) table_injective (h.project.symm ▸ he)
  have hp (i : Fin 42) : e.stacks (LeafRingSetupProgram.table i)=out.stacks i :=
    embedState_stack _ _ _ _ table_injective i
  refine ⟨n,hn,e,he',?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [LeafRingSetupProgram.table,out,Machine.state] using hp 27
  · simpa [LeafRingSetupProgram.table,out,Machine.state,preparedStore,ready,tapes,tableInputStore] using hp 5
  · simpa [LeafRingSetupProgram.table,out,Machine.state,preparedStore,ready,tapes,tableInputStore] using hp 12
  · simpa [LeafRingSetupProgram.table,out,Machine.state,preparedStore,ready,tapes,tableInputStore] using hp 24
  · simpa [LeafRingSetupProgram.table,out,Machine.state,preparedStore,ready,tapes,tableInputStore] using hp 22
  · simpa [LeafRingSetupProgram.table,out,Machine.state,preparedStore,ready,tapes,tableInputStore] using hp 17
  · intro i hi
    exact embedState_stack_frame _ _ _ _ _ hi


end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
