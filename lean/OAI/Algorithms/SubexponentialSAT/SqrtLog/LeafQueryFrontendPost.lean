import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendFinish
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgramExports

namespace OAI.Algorithms

/-! Paid persistent metadata export, offset construction, mask conversion, and
scratch cleanup after the guarded numeric bank has been computed. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
open LeafParametersProgram


abbrev Exported (m : Circuit.Model) (a : Data) : Prop :=
  (∀ i : Fin 8, a.stacks (Exports.destination (i.castAdd 8))=
    List.replicate (Exports.unaryValues m i) true) ∧
  (∀ i : Fin 8, BinaryArithmetic.toNat (a.stacks (Exports.destination (i.natAdd 8)))=
    m.val (Exports.binarySources i))

def postCommand : Code := .seq Exports.prepareCommand
  (.seq offsetCall (.seq lowMask clearPrivate))

noncomputable def postBudget (m : Circuit.Model) (prepared beforeClean : Data) (descending : List Bool) : ℕ :=
  Exports.prepareBudget m+
    LayoutOffsetProgram.budget (prepared.stacks 725) (prepared.stacks 720) (prepared.stacks 727)+
    (12*descending.length+8)+cleanupCost beforeClean

theorem export_destination_not_private (i : Fin 16) :
    (Exports.destination i).val < 340 ∨ 680 ≤ (Exports.destination i).val := by
  fin_cases i <;> decide

theorem postCommand_eval (a : Data) (m : Circuit.Model) (w : Bank.Words)
    (hs : Circuit.Shape m w)
    (hp : projectState Exports.bankRegs Exports.bank a=Bank.state (a.regs ∘ Exports.bankRegs) w)
    (hr : 0 < m.val 18) (hz : ∀ j,46 ≤ j.val → m.val j=0)
    (ho : Exports.OutputEmpty a) (ht : emptyRange a 648 680)
    (h134 : a.stacks 134=[]) (h141 : a.stacks 141=[])
    (descending : List Bool) (h338 : a.stacks 338=descending) :
    ∃ n b prepared beforeClean wf, Eval postCommand n a b ∧
      n ≤ postBudget m prepared beforeClean descending ∧
      Exported m b ∧
      BinaryArithmetic.toNat (b.stacks 141)=2*m.val 3*(8*m.val 21)^(2*m.val 29) ∧
      b.stacks 134=descending.reverse.map Bool.not ∧
      projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) wf ∧
      Circuit.Shape m wf ∧ b.regs 8=a.regs 8 ∧ emptyRange b 417 680 ∧
      (∀ i : Fin 768, (i.val < 340 ∨ 680 ≤ i.val) → i≠134 → i≠141 →
        (∀ j,Exports.destination j≠i) → b.stacks i=a.stacks i) := by
  have hscratch : Exports.Scratch a := ⟨ht _ (by decide) (by decide),ht _ (by decide) (by decide),
    ht _ (by decide) (by decide),ht _ (by decide) (by decide)⟩
  obtain ⟨ne,hne,rf,wb,hee,hsb,hsr⟩ := Exports.prepare_eval a m w hs hp hr hz ho hscratch
  let e := Exports.cleared (Exports.exportState (Exports.cached a rf wb))
  have ef (i : Fin 768) (hi : i.val < 340 ∨ 417 ≤ i.val) (hd : ∀ j,Exports.destination j≠i) :
      e.stacks i=a.stacks i := Exports.prepared_stack_frame a rf wb ho hscratch i hi hd
  have ez : emptyRange e 648 680 := by
    intro i hi hj
    apply (ef i (Or.inr (by omega)) ?_).trans (ht i hi hj)
    intro j heq
    have hv := congrArg Fin.val heq
    have hd := export_destination_not_private j
    omega
  have e141 : e.stacks 141=[] := (ef _ (Or.inl (by decide)) (by intro j; fin_cases j <;> decide)).trans h141
  obtain ⟨no,hno,o,heo,hov,hol,ofr,ogr⟩ := offset_eval e
    (fun i hi hj => ez i (by omega) (by omega)) e141
  have oz : emptyRange o 648 680 := by
    intro i hi hj
    exact (ofr i (by intro heq; subst i; norm_num at hi)).trans (ez i hi hj)
  have o134 : o.stacks 134=[] := (ofr _ (by decide)).trans
    ((ef _ (Or.inl (by decide)) (by intro j; fin_cases j <;> decide)).trans h134)
  have o338 : o.stacks 338=descending := (ofr _ (by decide)).trans
    ((ef _ (Or.inl (by decide)) (by intro j; fin_cases j <;> decide)).trans h338)
  obtain ⟨c,hec,hc134,hc668,cfr,cgr⟩ := lowMask_eval o descending o338 o134
    (oz _ (by decide) (by decide)) (oz _ (by decide) (by decide))
  have c679 : c.stacks 679=[] := (cfr _ (by decide) (by decide)).trans (oz _ (by decide) (by decide))
  have heclear := cleanup_eval c c679
  let b := cleaned c
  have bf (i : Fin 768) (hi : i.val < 417 ∨ 680 ≤ i.val) (h134 : i≠134) (h141 : i≠141) :
      b.stacks i=e.stacks i :=
    (cleaned_frame c i hi).trans ((cfr i h134 (by intro heq; subst i; omega)).trans (ofr i h141))
  have bexp : Exported m b := by
    constructor
    · intro i
      rw [bf _ (by have := export_destination_not_private (i.castAdd 8); omega)
        (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
      exact Exports.prepared_unary a rf m wb hsb ho hscratch i
    · intro i
      rw [bf _ (by have := export_destination_not_private (i.natAdd 8); omega)
        (by fin_cases i <;> decide) (by fin_cases i <;> decide)]
      exact Exports.prepared_binary a rf m wb hsb ho hscratch i
  refine ⟨ne+(no+((12*descending.length+8)+cleanupCost c)),b,e,c,Exports.restoredWords wb,
    hee.seq (heo.seq (hec.seq heclear)),?_,bexp,?_,?_,?_,hsr,?_,cleaned_empty c c679,?_⟩
  · dsimp [postBudget]; omega
  · have hb141 : b.stacks 141=o.stacks 141 :=
      (cleaned_frame c 141 (Or.inl (by decide))).trans (cfr _ (by decide) (by decide))
    have vB := Exports.prepared_binary a rf m wb hsb ho hscratch 5
    have vQ := Exports.prepared_binary a rf m wb hsb ho hscratch 0
    have vR := Exports.prepared_binary a rf m wb hsb ho hscratch 7
    change BinaryArithmetic.toNat (e.stacks 725)=m.val 3 at vB
    change BinaryArithmetic.toNat (e.stacks 720)=m.val 21 at vQ
    change BinaryArithmetic.toNat (e.stacks 727)=m.val 29 at vR
    simpa only [hb141,vB,vQ,vR] using hov
  · exact (cleaned_frame c _ (Or.inl (by decide))).trans hc134
  · have ep := Exports.restored_projection a rf wb
      (Exports.cached_empty a rf wb ho) (Exports.cached_scratch a rf wb hscratch)
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    have hbi : b.stacks (Exports.bank i)=e.stacks (Exports.bank i) := by
      apply bf
      · left; dsimp [Exports.bank]; have := i.isLt; omega
      · intro heq; have := congrArg Fin.val heq; dsimp [Exports.bank] at this; omega
      · intro heq; have := congrArg Fin.val heq; dsimp [Exports.bank] at this; omega
    exact hbi.trans (congrFun (congrArg StructuredProgram.State.stacks ep) i)
  · exact (cleaned_guard c).trans (cgr.trans (ogr.trans (Exports.prepared_register_frame a rf wb 8 (by decide))))
  · intro i hi h134 h141 hd
    exact (bf i (by omega) h134 h141).trans (ef i (by omega) hd)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
