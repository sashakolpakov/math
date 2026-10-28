import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PreparedNodeReadyBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPreparationState
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramNativeQuery
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramOutput

namespace OAI.Algorithms

/-! The parked query words are the bytes actually exported by packing and
preserved by arithmetic preparation. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram MulticolorTypes Subexp
open LeafHeadSetupProgram
attribute [local simp] Fin.coe_ofNat_eq_mod
variable {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data} {hg : Guard (q.input k)}
  {W V L : ℕ} (p : Query.Preparation q k a hg W V L)

 theorem out_parked (i : Fin 768) (hlo : 730 ≤ i.val) (hhi : i.val < 744) :
    p.out.stacks i=p.packed.stacks i := by
  apply p.arithmeticOutput.highFrame i (by omega)
  · intro h; have hv := congrArg Fin.val h; norm_num at hv; omega
  · intro h
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at h
    rcases h with h|h|h|h|h|h <;>
      have hv := congrArg Fin.val h <;> norm_num at hv <;> omega

 theorem parked_parameter (i : Fin 14) (h5 : i≠5) (h7 : i≠7) (h8 : i≠8) :
    p.out.stacks (LayoutMasters.high i)=p.front.stacks (LayoutMasters.low i) := by
  rw [out_parked p _ (by simp [LayoutMasters.high]) (by
    simp only [LayoutMasters.high]; have := i.isLt; omega),p.packingBytes]
  exact PackingCallerProgram.result_parameter p.front (Query.packingProblem q k hg)
    (Query.packing_empty p.front p.frontOutput.privateEmpty p.frontOutput.spare)
    p.firstWord p.remainingWords i h5 h7 h8

 theorem parked_words : p.out.stacks 735=
    (Native.queryInputs q k hg p.firstWord p.remainingWords ⟨0,(Query.packingProblem q k hg).hQ⟩).rows.flatten := by
  rw [out_parked p _ (by decide) (by decide),p.packingBytes]
  exact PackingCallerProgram.result_words p.front (Query.packingProblem q k hg)
    (Query.packing_empty p.front p.frontOutput.privateEmpty p.frontOutput.spare)
    p.firstWord p.remainingWords

 theorem parked_metadata : p.out.stacks 737=
    (Native.queryInputs q k hg p.firstWord p.remainingWords ⟨0,(Query.packingProblem q k hg).hQ⟩).metadata := by
  rw [out_parked p _ (by decide) (by decide),p.packingBytes]
  exact PackingCallerProgram.result_metadata p.front (Query.packingProblem q k hg)
    (Query.packing_empty p.front p.frontOutput.privateEmpty p.frontOutput.spare)
    p.firstWord p.remainingWords

 theorem parked_plans : p.out.stacks 738=PackingCallerProgram.planBits q.scopeRows
    (BinaryArithmetic.toNat q.ambient) q.forward := by
  rw [out_parked p _ (by decide) (by decide),p.packingBytes]
  exact PackingCallerProgram.result_plans p.front (Query.packingProblem q k hg)
    (Query.packing_empty p.front p.frontOutput.privateEmpty p.frontOutput.spare)
    p.firstWord p.remainingWords

 theorem packed_low_empty (i : Fin 14) : p.packed.stacks (LayoutMasters.low i)=[] := by
  rw [p.packingBytes]
  exact PackingCallerProgram.result_low _ _ _ _ i
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady

end

end OAI.Algorithms
