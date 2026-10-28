import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPackingEmpty
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendRegisterFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendUniform
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendExact

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The physical output required by the following native packing/ring stages. -/
structure FrontState (q : LeafQueryFrontend.Query) (k : ℕ) (a b : Data)
    (l : Fin 8 → ℕ) (w : Bank.Words) : Prop where
  hashCount : b.stacks 704=List.replicate q.rows.length true
  scopes : b.stacks 718=LeafStatisticsProgram.scopeBits q.scopeRows
  descending : b.stacks 338=LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)
  forward : b.stacks 719=q.forward
  low : b.stacks 134=q.forward.map Bool.not
  exported : LeafQueryFrontend.Exported (Execute.guardedModel (q.input k) l) b
  bank : projectState Exports.bankRegs Exports.bank b=Bank.state (b.regs ∘ Exports.bankRegs) w
  shape : Circuit.Shape (Execute.guardedModel (q.input k) l) w
  guard : b.regs 8=true ↔ Guard (q.input k)
  privateEmpty : LeafQueryFrontend.emptyRange b 417 680
  spare : PackingSpare b
  ambient : b.stacks 709=q.ambient
  frame : ∀i : Fin 768,(i.val < 340 ∨ 680 ≤ i.val) →
    i≠134 → i≠141 → i≠338 → i≠704 → i≠718 → i≠719 →
    (∀j,Exports.destination j≠i) → b.stacks i=a.stacks i
  registerFrame : ∀i : Fin 40,11 ≤ i.val → b.regs i=a.regs i
  offset : BinaryArithmetic.toNat (b.stacks 141)=
    2*(Execute.guardedModel (q.input k) l).val 3*
      (8*(Execute.guardedModel (q.input k) l).val 21)^
        (2*(Execute.guardedModel (q.input k) l).val 29)
  canonicalLengths : l=q.inputLengths k

theorem front_state (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hv : q.Valid) (hr : q.Ready a) (ho : q.OutputEmpty a) (hs : PackingSpare a) :
    ∃ n b l w,
      Eval (LeafQueryFrontend.frontend k) n a b ∧
      n ≤ q.inputBudget k ∧
      FrontState q k a b l w := by
  obtain ⟨n,b,counted,prepared,beforeClean,tau,l,w,he,hn,ht,h704,h718,h338,h719,h134,
    hex,h141,hbank,hshape,hguard,hclean,hframe,hcanonical⟩ :=
    LeafQueryFrontend.frontend_eval_with_inputLengths q k a hv hr ho
  refine ⟨n,b,l,w,he,LeafQueryFrontend.frontend_time_le q k hv hr ho he,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hframe,?_,h141,hcanonical⟩
  · exact h704
  · exact h718
  · exact h338
  · exact h719
  · exact h134
  · exact hex
  · exact hbank
  · exact hshape
  · exact hguard
  · exact hclean
  · exact packingSpare_of_frontend_frame a b hs hframe
  · exact (hframe _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)).trans hr.2.2.2.2.2.2.1
  · exact LeafQueryFrontend.frontend_register_frame k he

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
