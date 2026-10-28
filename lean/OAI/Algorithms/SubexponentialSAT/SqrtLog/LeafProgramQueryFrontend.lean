import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendRun

namespace OAI.Algorithms

/-! Native frontend entry from an actual marked-reference reader state. All
computed-size witnesses remain explicit in the paid budget. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram

def markedFrontend (k : ℕ) : Code := .seq markInput (LeafQueryFrontend.frontend k)

theorem marked_frontend_eval (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hv : q.Valid) (hc : CleanWork a) (hs : Sources q a)
    (hm : q.mark.isSome=true) (href : a.stacks 321=q.index.reverse) :
    ∃ n b counted prepared beforeClean tau l w,
      Eval (markedFrontend k) n a b ∧
      n ≤ 10*(a.stacks 321).length+10+
        LeafQueryFrontend.frontendBudget q k counted prepared beforeClean tau l ∧
      BinaryArithmetic.toNat tau=EarlyThreshold.threshold (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 704=List.replicate q.rows.length true ∧
      b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows ∧
      b.stacks 338=LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient) ∧
      b.stacks 719=q.forward ∧ b.stacks 134=q.forward.map Bool.not ∧
      LeafQueryFrontend.Exported (Execute.guardedModel (q.input k) l) b ∧
      BinaryArithmetic.toNat (b.stacks 141)=
        2*(Execute.guardedModel (q.input k) l).val 3*
        (8*(Execute.guardedModel (q.input k) l).val 21)^
          (2*(Execute.guardedModel (q.input k) l).val 29) ∧
      projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) w ∧
      Circuit.Shape (Execute.guardedModel (q.input k) l) w ∧
      (b.regs 8=true ↔ Guard (q.input k)) ∧ LeafQueryFrontend.emptyRange b 417 680 ∧
      (∀i : Fin 768,(i.val < 340 ∨ 680 ≤ i.val) →
        i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 → i≠705 → i≠706 → i≠699 →
        (∀j,Exports.destination j≠i) → b.stacks i=a.stacks i) := by
  have hready := marked_ready q a hc hs hm href
  have hempty : q.OutputEmpty (markedInput a) := marked_outputs_empty a hc
  obtain ⟨nf,b,counted,prepared,beforeClean,tau,l,w,he,hn,ht,h704,h718,h338,h719,h134,
    hex,h141,hbank,hshape,hguard,hclean,hframe⟩ :=
    LeafQueryFrontend.frontend_eval q k (markedInput a) hv hready hempty
  have hmark := markInput_eval a (hc 698 (by decide) (by decide))
    (hc 699 (by decide) (by decide))
  refine ⟨10*(a.stacks 321).length+10+nf,b,counted,prepared,beforeClean,tau,l,w,
    hmark.seq he,by omega,ht,h704,h718,h338,h719,h134,hex,h141,hbank,hshape,hguard,hclean,?_⟩
  intro i hi h134 h141 h338 h704 h718 h719 h705 h706 h699 hd
  exact (hframe i hi h134 h141 h338 h704 h718 h719 hd).trans
    (markedInput_frame a i h699 h705 h706)

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
