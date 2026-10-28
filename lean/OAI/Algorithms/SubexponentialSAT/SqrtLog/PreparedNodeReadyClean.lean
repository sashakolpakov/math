import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PreparedNodeReadyQuery
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PreparedNodeReadyFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PreparedNodeReadyPorts

namespace OAI.Algorithms

/-! Blank storage inherited from the actual query frontend and packing. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod
variable {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data} {hg : Guard (q.input k)}
  {W V L : ℕ} (p : Query.Preparation q k a hg W V L)

 theorem packed_low_blank (hb : NodeNative.Blank a) (i : Fin 768)
    (hi : i∈Node.cleanupPorts) (hn : i≠78) (hlo : i.val < 190) : p.packed.stacks i=[] := by
  by_cases hlow : 128 ≤ i.val ∧ i.val < 142
  · let j : Fin 14 := ⟨i.val-128,by omega⟩
    have hj : LayoutMasters.low j=i := by apply Fin.ext; simp only [LayoutMasters.low,j]; omega
    rw [←hj]
    exact packed_low_empty p j
  · rw [p.packingFrame i (Or.inl (by omega)) (by omega) (Or.inl (by omega))]
    rw [p.frontOutput.frame i (Or.inl (by omega))]
    · exact hb i hi hn
    all_goals first
      | (intro he; have hv := congrArg Fin.val he; norm_num at hv; omega)
      | (intro j he; have hv := congrArg Fin.val he
         fin_cases j <;> simp [Exports.destination] at hv <;> omega)

 theorem out_high_blank (hb : NodeNative.Blank a) (i : Fin 768)
    (hi : i∈Node.cleanupPorts) (hlo : 340 ≤ i.val) (hne : i≠699) : p.out.stacks i=[] := by
  by_cases h660 : i.val < 660
  · exact p.arithmeticOutput.privateEmpty i hlo h660
  have hregions := (Node.mem_cleanup i).mp hi
  have hhi : i.val < 713 := by omega
  have hnot : i∉([713,714,715,716,717,728] : List (Fin 768)) := by
    intro he
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at he
    rcases he with he|he|he|he|he|he <;>
      have hv := congrArg Fin.val he <;> norm_num at hv <;> omega
  rw [p.arithmeticOutput.highFrame i (by omega) hne hnot,
    p.packingFrame i (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))]
  by_cases h680 : i.val < 680
  · exact p.frontOutput.privateEmpty i (by omega) h680
  rw [p.frontOutput.frame i (Or.inr (by omega))]
  · exact hb i hi (by intro he; have hv := congrArg Fin.val he; norm_num at hv; omega)
  all_goals first
    | (intro he; have hv := congrArg Fin.val he; norm_num at hv; omega)
    | (intro j he; have hv := congrArg Fin.val he
       fin_cases j <;> simp [Exports.destination] at hv <;> omega)
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady

end

end OAI.Algorithms
