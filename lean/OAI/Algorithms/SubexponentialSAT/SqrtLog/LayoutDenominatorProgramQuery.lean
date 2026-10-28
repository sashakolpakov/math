import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQueryRun
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgramNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramConstantsModel

namespace OAI.Algorithms

/-! A denominator constructor consuming the actual ring-setup certificate.
The inverse-half fact comes from that executed setup, and the power is then
computed by the fixed native multiplication loop in the private bank. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
open SubexpLiftRing SubexpQuarticRing IntegerRingLiftProgram

private theorem ready_of_caches (a : LocalData) (t d : ℕ) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (u : RingProgram.ScalarCode 3 t) (e : LeafRingSetupProgram.Data)
    (h : LeafRingSetupProgram.RingCaches t d model M cache u e)
    (hf : ∀i : Fin 640,i.val < 340 → a.stacks (LeafRingSetupProgram.wideStacks i)=e.stacks i) :
    CachedReady t model M cache
      (LeafProgram.Constants.constantCode d cache.zero cache.zero)
      (LeafProgram.Constants.constantCode d cache.one cache.zero)
      (LeafProgram.Constants.constantCode d cache.minusOne cache.zero) (localInput a) := by
  have h194 := (hf 194 (by decide)).trans h.modulus
  have h201 := (hf 201 (by decide)).trans h.table
  have h202 := congrArg List.length (hf 202 (by decide))
  have h203 := (hf 203 (by decide)).trans h.scalarZero
  have h204 := congrArg List.length (hf 204 (by decide))
  have h280 := (hf 280 (by decide)).trans h.fullZero
  have h207 := (hf 207 (by decide)).trans h.fullOne
  have h211 := (hf 211 (by decide)).trans h.fullMinusOne
  refine ⟨?_,by simp [Clean,localInput],?_,?_,?_,by simp [localInput],by simp [localInput],
    by simp [localInput],by simp [localInput]⟩
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · refine ⟨by simp [localInput],?_⟩
      intro i
      fin_cases i <;> simp [ReconstructionProgram.RingAdapter.ports,
        ReconstructionProgram.RingAdapter.finalNative,ReconstructionProgram.RingAdapter.nativeStacks,localInput]
    · simpa [localInput,LeafRingSetupProgram.wideStacks] using h194
    · simpa [localInput,LeafRingSetupProgram.wideStacks] using h202.trans h.width
    · simpa [localInput,LeafRingSetupProgram.wideStacks] using h203
    · simpa [localInput,LeafRingSetupProgram.wideStacks,
        RingProgramTable.modelTable,IntegerRingLiftProgram.modelTable] using h201
    · simpa [localInput,LeafRingSetupProgram.wideStacks] using h204.trans h.degree
  · simpa [localInput,LeafRingSetupProgram.wideStacks,
      LeafProgram.Constants.constantCode_flat] using h280
  · simpa [localInput,LeafRingSetupProgram.wideStacks,
      LeafProgram.Constants.constantCode_flat] using h207
  · simpa [localInput,LeafRingSetupProgram.wideStacks,
      LeafProgram.Constants.constantCode_flat] using h211

def value (t : ℕ) {d : ℕ} (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (u : RingProgram.ScalarCode 3 t) (R : ℕ) : ModelCode t d :=
  LayoutDenominatorProgram.value t model M cache
    (LeafProgram.Constants.constantCode d cache.zero cache.zero)
    (LeafProgram.Constants.constantCode d cache.one cache.zero)
    (LeafProgram.Constants.constantCode d cache.minusOne cache.zero) u.val R

/-- The actual per-query call after ring setup and interpolation. No
inverse-denominator word is an input: stack 728 starts empty and is filled by
an executed binary-to-ring lift followed by R-1 native multiplications. -/
theorem produced_command_eval (a : Data) (m : LeafParametersProgram.Circuit.Model)
    (ht : 0 < m.val 33) (hd : 0 < m.val 34)
    (M : SubexpPreparedQuartic.Modulus 3 (m.val 33))
    (cache : RingProgram.ScalarCache 3 (m.val 33))
    (u : RingProgram.ScalarCode 3 (m.val 33)) (e : LeafRingSetupProgram.Data)
    (hp : LeafRingSetupProgram.Produced m hd M cache u e)
    (hf : ∀i : Fin 640,i.val < 340 → a.stacks (LeafRingSetupProgram.wideStacks i)=e.stacks i)
    (hc : ∀i : Fin 768,340 ≤ i.val → i.val < 596 → a.stacks i=[])
    (hout : a.stacks 728=[]) (W : ℕ) (hw : WordBound W a) :
    ∃ n ≤ budget (a.stacks 740).length (m.val 33) (m.val 34) W, ∃ out : Data,
      Eval command n a out ∧
      out.stacks=Function.update a.stacks 728 (RingProgram.flat
        (value (m.val 33) (IrreducibleSearch.data hd) M cache u (a.stacks 740).length)) ∧
      (RingProgram.modelRing (m.val 33) ht hd (IrreducibleSearch.data hd) M cache).decode
        (value (m.val 33) (IrreducibleSearch.data hd) M cache u (a.stacks 740).length) *
        (2 : (IrreducibleSearch.data hd).O (m.val 33)) ^ ((a.stacks 740).length-1)=1 ∧
      (∀i : Fin 40,16 ≤ i.val → out.regs i=a.regs i) := by
  have hready := ready_of_caches (projectState registers id a) (m.val 33) (m.val 34)
    (IrreducibleSearch.data hd) M cache u e hp.caches hf
  have hu : a.stacks 253=u.val := (hf 253 (by decide)).trans hp.caches.half
  have hsize : m.val 34*baseWidth 3 (m.val 33) ≤ W := by
    have hh := hw 280
    have he : a.stacks 280=RingProgram.flat
        (LeafProgram.Constants.constantCode (m.val 34) cache.zero cache.zero) := by
      rw [LeafProgram.Constants.constantCode_flat]
      exact (hf 280 (by decide)).trans hp.caches.fullZero
    rw [he,RingProgram.flat_length] at hh
    exact hh
  obtain ⟨n,hn,out,he,hout',hr⟩ := command_eval a (m.val 33) (IrreducibleSearch.data hd) M cache
    _ _ _ u hp.caches.canonical hready hu
    (fun i hi => hc i ((mem_bank i).mp hi).1 ((mem_bank i).mp hi).2) hout W hw hsize
  refine ⟨n,hn,out,he,hout',?_,hr⟩
  exact LayoutDenominatorProgram.value_inverse (m.val 33) ht hd (IrreducibleSearch.data hd)
    M cache _ _ _
    (LeafProgram.Constants.zero_decode _ ht hd _ M cache)
    (LeafProgram.Constants.one_decode _ ht hd _ M cache)
    (LeafProgram.Constants.minusOne_decode _ ht hd _ M cache)
    u hp.caches.inverse _

/-- The storage cost is linear in the largest physically present word. The
remaining budget is the checked polynomial native denominator budget. -/
theorem budget_polynomial (R t d W : ℕ) :
    budget R t d W ≤ LayoutDenominatorProgram.polynomialBudget R (baseWidth 3 t) d + 600*(W+2) :=
  Nat.add_le_add_right (LayoutDenominatorProgram.budget_polynomial R t d) _

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
