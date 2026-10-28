import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopNative

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop
attribute [local simp] Fin.coe_ofNat_eq_mod
open SubexponentialSAT BitProgram StructuredCalls MomentsProgram
open IdempotentApplyProgram.Bounds

def byteBound (n B d u J : ℕ) : ℕ :=
  byteCapacity n B d u J (capacity (Finset.univ : Finset (Fin n)) u J)

def commandBudget (n B d u J C : ℕ) (ids : List ℕ) : ℕ :=
  7*(ProgramEncoding.encodeRecords (records ids)).length+
    16*byteBound n B d u J+loopBudget C ids+18

theorem command_eval {n B d : ℕ} (u J : ℕ)
    (step : Raw n B d → ℕ → Raw n B d → Prop)
    (ready : (Fin 768 → List Bool) → Prop) (eligible : ℕ → Prop) (T C : ℕ)
    (contract : CallbackContract u J step ready eligible T C)
    (a : Factor.Data) (ha : ready a.stacks) (ids : List ℕ) (one : Raw n B d)
    (hg : Good Finset.univ u J one) (hids : ∀ id ∈ ids, eligible id)
    (hlen : (ProgramEncoding.encodeRecords (records ids)).length ≤ T)
    (h175 : a.stacks 175=ProgramEncoding.encodeRecords (records ids))
    (h69 : a.stacks 69=Product.bytes one)
    (h149 : a.stacks 149=[]) (h150 : a.stacks 150=[]) (h151 : a.stacks 151=[])
    (h67 : a.stacks 67=[]) (h159 : a.stacks 159=[]) :
    ∃ out, Good Finset.univ u J out ∧ RunRel step ids one out ∧
      ∃ k ≤ commandBudget n B d u J C ids, ∃ rr,
        Eval Factor.command k a ⟨rr,Function.update a.stacks 67 (Product.bytes out)⟩ := by
  let a1 := SubexpScanPrimitives.afterCopy a 175 150 0 1
  let a2 := SubexpScanPrimitives.afterCopy a1 69 151 0 1
  have h1 : Eval (Factor.copy 175 150) (7*(a.stacks 175).length+5) a a1 :=
    SubexpScanPrimitives.copy_eval a 175 150 159 0 1 (by decide) (by decide) (by decide) (by decide) h159
  have h2 : Eval (Factor.copy 69 151) (7*(a1.stacks 69).length+5) a1 a2 :=
    SubexpScanPrimitives.copy_eval a1 69 151 159 0 1 (by decide) (by decide) (by decide) (by decide)
      (by simpa [a1,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks] using h159)
  have hinput : a2=state a.stacks a2.regs one (ProgramEncoding.encodeRecords (records ids)) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases h1 : i=149 <;> by_cases h2 : i=150 <;> by_cases h3 : i=151 <;>
        simp_all [a2,a1,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks]
  obtain ⟨out,ho,hr,nl,hl,rr,he⟩ := loop_eval u J step ready eligible T C contract a.stacks ha ids one
    a2.regs hg hids hlen
  rw [← hinput] at he
  let b := state a.stacks rr out [] []
  have h3 := Factor.move_eval b 151 67 (by decide) (by decide) (by decide)
    (by simpa [b,state] using h159)
  have hout : Factor.moved b 151 67 =
      ⟨(Factor.moved b 151 67).regs,Function.update a.stacks 67 (Product.bytes out)⟩ := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      by_cases h1 : i=149 <;> by_cases h2 : i=150 <;> by_cases h3 : i=151 <;>
        by_cases h4 : i=67 <;>
        simp [b,state,h1,h2,h3,h4,h149,h150,h151,h67]
  rw [hout] at h3
  have honeBound := bytes_le_capacity Finset.univ u J one hg
  have houtBound := bytes_le_capacity Finset.univ u J out ho
  refine ⟨out,ho,hr,(7*(a.stacks 175).length+5)+((7*(a1.stacks 69).length+5)+
    (nl+(9*(b.stacks 151).length+8))),?_,_,h1.seq (h2.seq (he.seq h3))⟩
  dsimp [commandBudget,byteBound]
  simp only [h175] at *
  have h69' : a1.stacks 69=Product.bytes one := by
    simpa [a1,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks] using h69
  simp only [h69']
  have hb151 : b.stacks 151=Product.bytes out := by simp [b,state]
  rw [hb151]
  omega
end SubexponentialSAT.SqrtLog.LeafProgram.FactorLoop

end OAI.Algorithms
