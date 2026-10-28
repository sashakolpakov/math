import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgramInitialBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSetupOuterCostInitialMajorant

namespace OAI.Algorithms

/-! Uniform cost of the actual complete initial-code producer, with all
physical word-length premises discharged from its trace. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage Filter
open scoped Topology

theorem initialCode_resource_eval :
    ∃ C d p : ℕ, ∀ q : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ (a : Data) W (records : List (List Bool)) B,
      WordBound W a → (∀ i : Fin 896, i.val ≤ 782 → a.stacks i=[]) →
      a.stacks 784=Encoding.encodeList id records → records≠[] →
      0 < B → BinaryArithmetic.toNat (a.stacks 786)=B →
      BinaryArithmetic.toNat (a.stacks 785)=n →
      records.length ≤ n*B → B ≤ Asymptotic.L n^q →
      ∃ steps b, ∃ (s : SparseCode.SuppliedShifts records.length B)
        (Q : SparseCode.SuppliedLocal records.length B),
      Eval initialCode steps a b ∧
      steps ≤ CodeSetupOuterCost.setupMajorant C d q n*(W+1)^p ∧
      StartReady b n records.length B ∧
      b.stacks 777=HashSelectProgram.candidateEncoding
        (LeafScopeResourceBounds.initialPayloads (b.stacks 768).length
          (CodeRowsProgram.serializedRows records.length s Q)) ∧
      WalshExistence.Good (SparseCode.gapDenom records.length B) s ∧
      SparseCode.HasDistance Q
        (SparseCode.degree records.length B/(100*B*SparseCode.logSize records.length)+1) ∧
      (∀ i : Fin 896, 784 ≤ i.val → i.val < 800 → b.stacks i=a.stacks i) := by
  obtain ⟨C,d,p,hbound⟩ := CodeSetupOuterCost.initial_resource_bound
  refine ⟨C,d,p,?_⟩
  intro q
  filter_upwards [hbound q] with n hn
  intro a W records B hW hempty hformula hm hB hBv hnv hmn hBn
  obtain ⟨steps,b,countWord,qword,Dword,s,Q,he,hsteps,hql,hDl,hcl,hml,hBl,
      hready,hwidth,hrows,hs,hQ,hframe⟩ :=
    initialCode_eval_with_lengths a W records B hW hempty hformula hm hB hBv
  have hr : (Encoding.encodeList id records).length ≤ W := by
    rw [←hformula]; exact hW 784
  have hcost := hn records.length B W records (b.stacks 782) (a.stacks 786)
    qword Dword countWord s Q (List.length_pos_iff.mpr hm) hB hmn hBn hr hml hBl hcl hql hDl
  have hc : countWord=b.stacks 768 := hwidth.symm.trans hready.width
  refine ⟨steps,b,s,Q,he,hsteps.trans hcost,?_,?_,hs,hQ,hframe⟩
  · simpa only [hnv] using hready
  · simpa only [hc] using hrows

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
