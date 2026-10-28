import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeMass

namespace OAI.Algorithms

/-! The protected mass callback restores every non-selector register and every
non-score stack, including the arbitrary tail used for register preservation. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative
open SubexponentialSAT BitProgram StructuredCalls LeafOuterProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

@[simp] theorem saved_massPrecision (a : Data) :
    massPrecision (savedRegisters callerRegisters a)=massPrecision a := by
  simp [massPrecision,savedRegisters_eq]
@[simp] theorem saved_massRecords (a : Data) :
    massRecords (savedRegisters callerRegisters a)=massRecords a := by
  simp [massRecords,savedRegisters_eq]

theorem saved_WorkerEmpty (a : Data) (ha : WorkerEmpty a) :
    WorkerEmpty (savedRegisters callerRegisters a) := by
  intro i
  have hn : workerStack i≠895 := by
    intro h
    have hv := congrArg (fun x : Fin 896 => x.val) h
    have := i.isLt
    change i.val=895 at hv
    omega
  simpa only [savedRegisters_eq,Function.update_of_ne hn] using ha i

noncomputable def massBudget (a : Data) (queryCost width : List Bool → ℕ) (z : ℕ) : ℕ :=
  massBodyBudget (savedRegisters callerRegisters a) queryCost width z+64

theorem mass_eval (k : ℕ) (a : Data) (ha : WorkerEmpty a)
    (hm : BinaryArithmetic.toNat (a.stacks 782)≠0)
    (count queryCost width : List Bool → ℕ) (valid : List Bool → Prop)
    (hq : MassQueries k (savedRegisters callerRegisters a) count queryCost width valid)
    (hr : ∀ bits∈massRecords a, valid bits) (z : ℕ)
    (hz : (List.map count (massRecords a)).sum=z) (hcap : z < 2^massPrecision a) :
    ∃ t b, t ≤ massBudget a queryCost width z ∧ Eval (mass k) t a b ∧
      b.stacks=Function.update a.stacks 769 (SubexpLiftRing.fixedBits (massPrecision a) z) ∧
      (∀ i : Fin 40, (8 : ℕ) ≤ i.val → b.regs i=a.regs i) := by
  let s := savedRegisters callerRegisters a
  have hs : WorkerEmpty s := saved_WorkerEmpty a ha
  have hsm : BinaryArithmetic.toNat (s.stacks 782)≠0 := by
    simpa [s,savedRegisters_eq] using hm
  obtain ⟨t,b,ht,he,hb⟩ := massBody_eval k s hs hsm count queryCost width valid hq
    (by simpa [s] using hr) z (by simpa [s] using hz) (by simpa [s] using hcap)
  have hb895 : b.stacks 895=s.stacks 895 := by simp [hb]
  obtain ⟨c,hc,hregs,h895,hframe⟩ := protectCaller_eval (massBody k) a b t he hb895
  refine ⟨t+64,c,Nat.add_le_add_right ht 64,hc,?_,hregs⟩
  funext i
  by_cases hi : i=895
  · subst i; simpa using h895
  · rw [hframe i hi,hb]
    by_cases ho : i=769
    · subst i; simp [s]
    · simp [Function.update_of_ne ho,s,savedRegisters_eq,hi]

end SubexponentialSAT.SqrtLog.LeafOuterNative

end OAI.Algorithms
