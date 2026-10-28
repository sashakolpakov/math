import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendPost
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendGrowth

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

def offsetModelBudget (m : Circuit.Model) : ℕ :=
  5000*(2*m.val 29+1)^2*(m.len 3+m.len 21+m.len 29+11)^2

def postPrefixBudget (m : Circuit.Model) (n : ℕ) : ℕ :=
  Exports.prepareBudget m+offsetModelBudget m+12*n+8

def postUniformBudget (m : Circuit.Model) (n A : ℕ) : ℕ :=
  525*postPrefixBudget m n+524*A+789

/-- Input-only bound for the export/offset/mask/cleanup suffix. The live-word
bound A is propagated from the preceding actual evaluation. -/
theorem postCommand_eval_uniform (a : Data) (m : Circuit.Model) (w : Bank.Words)
    (hs : Circuit.Shape m w)
    (hp : projectState Exports.bankRegs Exports.bank a=Bank.state (a.regs ∘ Exports.bankRegs) w)
    (hr : 0 < m.val 18) (hz : ∀ j,46 ≤ j.val → m.val j=0)
    (ho : Exports.OutputEmpty a) (ht : emptyRange a 648 680)
    (h134 : a.stacks 134=[]) (h141 : a.stacks 141=[])
    (descending : List Bool) (h338 : a.stacks 338=descending)
    (A : ℕ) (ha : ∀ i∈cleanupPorts, (a.stacks i).length ≤ A) :
    ∃ n b, Eval postCommand n a b ∧ n ≤ postUniformBudget m descending.length A := by
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
  have hbB := Exports.prepared_binary_length a rf m wb hsb ho hscratch 5
  have hbQ := Exports.prepared_binary_length a rf m wb hsb ho hscratch 0
  have hbR := Exports.prepared_binary_length a rf m wb hsb ho hscratch 7
  have hvR := Exports.prepared_binary a rf m wb hsb ho hscratch 7
  change (e.stacks 725).length ≤ m.len 3 at hbB
  change (e.stacks 720).length ≤ m.len 21 at hbQ
  change (e.stacks 727).length ≤ m.len 29 at hbR
  change BinaryArithmetic.toNat (e.stacks 727)=m.val 29 at hvR
  have hbo : LayoutOffsetProgram.budget (e.stacks 725) (e.stacks 720) (e.stacks 727) ≤ offsetModelBudget m := by
    rw [LayoutOffsetProgram.budget_eq,hvR]
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    omega
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
  have hclean := cleanupCost_le_after_eval (hee.seq (heo.seq hec)) ha
  refine ⟨ne+(no+(12*descending.length+8+cleanupCost c)),cleaned c,
    hee.seq (heo.seq (hec.seq heclear)),?_⟩
  unfold postUniformBudget postPrefixBudget
  omega

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
