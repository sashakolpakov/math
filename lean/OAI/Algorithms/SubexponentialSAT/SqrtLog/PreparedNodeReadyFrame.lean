import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PreparedNodeReadyBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQuerySetup
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgramWide

namespace OAI.Algorithms

/-! The real query, branch, and collector state maps retain parked inputs
and blank node scratch. These are data equalities, not execution premises. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady
open SubexponentialSAT BitProgram StructuredCalls LeafHeadSetupProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

private theorem cleanupPorts_middle (i : Fin 768) (hlo : 192 ≤ i.val) (hhi : i.val < 340) :
    i ∉ Node.cleanupPorts := by
  intro h
  have hh := (Node.mem_cleanup i).mp h
  omega

private theorem cleanupPorts_gap (i : Fin 768) (hlo : 700 ≤ i.val) (hhi : i.val < 710) :
    i ∉ Node.cleanupPorts := by
  intro h
  have hh := (Node.mem_cleanup i).mp h
  omega

private theorem cleanupPorts_333 : (333 : Fin 768) ∉ Node.cleanupPorts :=
  cleanupPorts_middle 333 (by norm_num) (by norm_num)
private theorem cleanupPorts_330 : (330 : Fin 768) ∉ Node.cleanupPorts :=
  cleanupPorts_middle 330 (by norm_num) (by norm_num)
private theorem cleanupPorts_702 : (702 : Fin 768) ∉ Node.cleanupPorts :=
  cleanupPorts_gap 702 (by norm_num) (by norm_num)
private theorem cleanupPorts_703 : (703 : Fin 768) ∉ Node.cleanupPorts :=
  cleanupPorts_gap 703 (by norm_num) (by norm_num)
private theorem cleanupPorts_301 : (301 : Fin 768) ∉ Node.cleanupPorts :=
  cleanupPorts_middle 301 (by norm_num) (by norm_num)
private theorem cleanupPorts_302 : (302 : Fin 768) ∉ Node.cleanupPorts :=
  cleanupPorts_middle 302 (by norm_num) (by norm_num)
private theorem cleanupPorts_303 : (303 : Fin 768) ∉ Node.cleanupPorts :=
  cleanupPorts_middle 303 (by norm_num) (by norm_num)
private theorem cleanupPorts_304 : (304 : Fin 768) ∉ Node.cleanupPorts :=
  cleanupPorts_middle 304 (by norm_num) (by norm_num)
private theorem cleanupPorts_305 : (305 : Fin 768) ∉ Node.cleanupPorts :=
  cleanupPorts_middle 305 (by norm_num) (by norm_num)
private theorem cleanupPorts_307 : (307 : Fin 768) ∉ Node.cleanupPorts :=
  cleanupPorts_middle 307 (by norm_num) (by norm_num)
private theorem cleanupPorts_102 : (102 : Fin 768) ∉ Node.cleanupPorts := by
  intro h
  have hh := (Node.mem_cleanup 102).mp h
  norm_num at hh
private theorem cleanupPorts_256 : (256 : Fin 768) ∉ Node.cleanupPorts :=
  cleanupPorts_middle 256 (by norm_num) (by norm_num)
private theorem cleanupPorts_265 : (265 : Fin 768) ∉ Node.cleanupPorts :=
  cleanupPorts_middle 265 (by norm_num) (by norm_num)

attribute [local irreducible] Count.Prepare.ports

 theorem parked_prepared {s : Native.Inputs} {a : Data} (h : Parked s a) :
    Parked s (Query.prepared a) := by
  apply h.congr
  intro i hi hj
  exact (Count.Prepare.output_parked _ i hi).trans
    (Samples.prepared_frame a i (by intro he; have := congrArg Fin.val he; norm_num at this; omega)
      (by intro he; have := congrArg Fin.val he; norm_num at this; omega))

 theorem parked_maskCopied {s : Native.Inputs} {a : Data} (h : Parked s a) :
    Parked s (Marked.Wide.maskCopied a) := by
  apply h.congr
  intro i hi hj
  exact Marked.Wide.maskCopied_frame a i (by
    intro he; have := congrArg Fin.val he; norm_num at this; omega)

 theorem parked_highContext {s : Native.Inputs} {a : Data} (h : Parked s a)
    (regs : Fin 4 → Bool) (high : List Bool) :
    Parked s (LeafHighContextProgram.finished a regs high) := by
  apply h.congr
  intro i hi hj
  apply LeafHighContextProgram.finished_frame
  intro he
  simp only [LeafHighContextProgram.changed,List.mem_cons,List.mem_nil_iff,or_false] at he
  rcases he with he|he|he|he|he|he|he|he <;>
    have := congrArg Fin.val he <;> norm_num at this <;> omega

 theorem parked_setCounter {s : Native.Inputs} {a : Data} (h : Parked s a)
    (bits : List Bool) : Parked s ⟨a.regs,Function.update a.stacks 330 bits⟩ := by
  apply h.congr
  intro i hi hj
  exact Function.update_of_ne (by intro he; have := congrArg Fin.val he; norm_num at this; omega) _ _

 theorem prepared_blank (a : Data)
    (h : ∀ i∈Node.cleanupPorts,i≠78 → i≠190 → i≠191 → i≠699 → a.stacks i=[]) :
    NodeNative.Blank (Query.prepared a) := by
  intro i hi hn
  change BankRoutines.clearBankStacks Count.Prepare.ports
    (Function.update (Samples.prepared a).stacks 699 []) i=[]
  by_cases hc : i∈Count.Prepare.ports
  · simp [BankRoutines.clearBankStacks,hc]
  simp only [BankRoutines.clearBankStacks,ite_eq_right hc]
  by_cases ht : i=699
  · subst i; simp
  rw [Function.update_of_ne ht,Samples.prepared_stacks]
  by_cases h190 : i=190
  · subst i; simp
  by_cases h191 : i=191
  · subst i; simp
  simp only [Function.update_of_ne h190,Function.update_of_ne h191]
  exact h i hi hn h190 h191 ht

 theorem maskCopied_blank {a : Data} (h : NodeNative.Blank a) :
    NodeNative.Blank (Marked.Wide.maskCopied a) := by
  intro i hi hn
  have ht : i≠333 := by intro he; subst i; exact cleanupPorts_333 hi
  exact (Marked.Wide.maskCopied_frame a i ht).trans (h i hi hn)

 theorem setCounter_blank {a : Data} (h : NodeNative.Blank a) (bits : List Bool) :
    NodeNative.Blank ⟨a.regs,Function.update a.stacks 330 bits⟩ := by
  intro i hi hn
  have ht : i≠330 := by intro he; subst i; exact cleanupPorts_330 hi
  exact (Function.update_of_ne ht _ _).trans (h i hi hn)

 theorem highContext_blank {a : Data} (h : NodeNative.Blank a)
    (regs : Fin 4 → Bool) (high : List Bool) :
    NodeNative.Blank (LeafHighContextProgram.finished a regs high) := by
  intro i hi hn
  by_cases hs : i∈LeafHighContextProgram.scratch
  · exact LeafHighContextProgram.finished_scratch a regs high i hs
  have hc : i∉LeafHighContextProgram.changed := by
    intro he
    simp only [LeafHighContextProgram.changed,List.mem_cons,List.mem_nil_iff,or_false] at he
    rcases he with he|he|he|he|he|he|he|he
    · subst i; exact cleanupPorts_702 hi
    · subst i; exact cleanupPorts_703 hi
    all_goals subst i; exact hs (by decide)
  exact (LeafHighContextProgram.finished_frame a regs high i hc).trans (h i hi hn)

 theorem collector_ready (s : Native.Inputs) (regs : Fin 40 → Bool)
    (store : LeafNodeSamplesProgram.Store)
    (hp : Parked s ⟨regs,store.frame⟩) (hb : NodeNative.Blank ⟨regs,store.frame⟩)
    (hn : store.index=unary s.node.val) (hs : store.shape=[]) :
    NodeNative.Ready s (LeafNodeSamplesProgram.state regs store) := by
  have hp' : Parked s (LeafNodeSamplesProgram.state regs store) := by
    apply hp.congr
    intro i hi hj
    have ne (j : Fin 768) (hj : j.val < 730) : i≠j := by
      intro he; have := congrArg Fin.val he; omega
    simp [LeafNodeSamplesProgram.state,LeafNodeSamplesProgram.tapes,
      ne 301 (by decide),ne 302 (by decide),ne 303 (by decide),ne 304 (by decide),
      ne 305 (by decide),ne 307 (by decide),ne 78 (by decide),ne 102 (by decide),
      ne 104 (by decide),ne 256 (by decide),ne 265 (by decide)]
  apply hp'.ready
  · intro i hi hn'
    by_cases h104 : i=104
    · subst i; simpa [LeafNodeSamplesProgram.state,LeafNodeSamplesProgram.tapes] using hs
    have ne (j : Fin 768) (hj : j∉Node.cleanupPorts) : i≠j := by
      intro he; subst i; exact hj hi
    change LeafNodeSamplesProgram.tapes store i=[]
    simp only [LeafNodeSamplesProgram.tapes,ite_eq_right (ne 301 cleanupPorts_301),
      ite_eq_right (ne 302 cleanupPorts_302),ite_eq_right (ne 303 cleanupPorts_303),
      ite_eq_right (ne 304 cleanupPorts_304),ite_eq_right (ne 305 cleanupPorts_305),
      ite_eq_right (ne 307 cleanupPorts_307),ite_eq_right hn',
      ite_eq_right (ne 102 cleanupPorts_102),ite_eq_right h104,
      ite_eq_right (ne 256 cleanupPorts_256),ite_eq_right (ne 265 cleanupPorts_265)]
    exact hb i hi hn'
  · simpa [LeafNodeSamplesProgram.state,LeafNodeSamplesProgram.tapes] using hn
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady

end

end OAI.Algorithms
