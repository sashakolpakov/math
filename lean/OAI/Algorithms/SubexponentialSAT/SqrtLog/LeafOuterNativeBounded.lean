import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeLocalBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeWidth

namespace OAI.Algorithms

/-! A single native mass bound using relevant input words and paid query
time. The output-width term is derived from the same query execution. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafOuterProgram LeafProgram

theorem massQueries_width_from_cost (k : ℕ) (a : Data)
    (count queryCost width : List Bool → ℕ) (valid : List Bool → Prop)
    (hq : MassQueries k a count queryCost width valid) :
    MassQueries k a count queryCost (fun bits => queryCost bits+1) valid := by
  intro b hb
  exact query_width_from_cost _ count queryCost width _ valid (hq b hb)

theorem mass_eval_bounded_sources (k : ℕ) (a : Data) (L Q : ℕ)
    (ha : WorkerEmpty a)
    (hs : ∀ i, MassSource i → (a.stacks i).length ≤ L)
    (hm : BinaryArithmetic.toNat (a.stacks 782)≠0)
    (count queryCost width : List Bool → ℕ) (valid : List Bool → Prop)
    (hq : MassQueries k (savedRegisters callerRegisters a) count queryCost width valid)
    (hr : ∀ bits∈massRecords a, valid bits)
    (hQ : ∀ bits∈massRecords a, queryCost bits ≤ Q)
    (z : ℕ) (hz : (List.map count (massRecords a)).sum=z)
    (hcap : z < 2^massPrecision a) :
    ∃ t b, t ≤ CounterPrograms.value (a.stacks 782)*Q+
        overhead L (CounterPrograms.value (a.stacks 782)) (massPrecision a) (Q+1)+64 ∧
      Eval (mass k) t a b ∧
      b.stacks=Function.update a.stacks 769 (SubexpLiftRing.fixedBits (massPrecision a) z) ∧
      (∀ i : Fin 40, 8 ≤ i.val → b.regs i=a.regs i) := by
  have hq' := massQueries_width_from_cost k (savedRegisters callerRegisters a)
    count queryCost width valid hq
  obtain ⟨t,b,ht,he,hb,hregs⟩ := mass_eval k a ha hm count queryCost
    (fun bits => queryCost bits+1) valid hq' hr z hz hcap
  have hbound := massBudget_le_sources a L Q (Q+1) z ha hs queryCost
    (fun bits => queryCost bits+1) hQ (fun bits hb => Nat.add_le_add_right (hQ bits hb) 1)
  exact ⟨t,b,ht.trans hbound,he,hb,hregs⟩

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms
