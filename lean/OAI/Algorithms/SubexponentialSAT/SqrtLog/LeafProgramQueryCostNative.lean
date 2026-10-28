import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostComponents
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryMaskedNative

namespace OAI.Algorithms

/-! Attach the measured envelope to the actual native query execution. The
residual specification is the semantic branch contract; its arbitrary budget
is tightened to the explicit residual envelope before the query is run. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram ProducedQueryResources

 theorem capped_context {a : Data} {ready : (Fin 763→List Bool)→Prop}
    {count B width : ℕ} (ctx : Marked.Wide.BranchContext Residual.command a ready count B width)
    (U K : ℕ) (hs : ctx.stepBudget ≤ residualCap U K) (hr : ctx.referenceBound ≤ U) :
    Nonempty (Marked.Wide.BranchContext Residual.command a ready count
      (Marked.Wide.branchTime a (residualCap U K) ctx.stepWidth U) width) := by
  refine ⟨{ctx with timeBound := ?_}⟩
  dsimp only [Marked.Wide.branchTime]
  gcongr

 theorem copied_mask_le {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Preparation q k a hg W V L)
    (occurrence qi : ℕ) (hw : ∀i,(a.stacks i).length ≤ W)
    (hz : (prepared p.out).stacks 333=[]) :
    ((Marked.Wide.maskCopied (prepared p.out)).stacks 333).length ≤ ordinaryCap p occurrence qi ∧
    2^HighIncidenceProgram.Branches.trueCount ((Marked.Wide.maskCopied (prepared p.out)).stacks 333) ≤
      CostAssembly.assembledWork k (ambient q) (resources q k occurrence qi hg p.firstWord p.remainingWords) := by
  rw [Marked.Wide.maskCopied_mask _ hz]
  refine ⟨prepared_width_le p occurrence qi hw 338,?_⟩
  rw [Width.prepared_mask]
  exact branches_le_assembled p occurrence qi

 theorem marked_measured (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hg : Guard (q.input k)) (W V L : ℕ)
    (p : Preparation q k (markedInput (Carried.reference a)) hg W V L)
    (hc : CleanWork a) (hw : ∀i,((markedInput (Carried.reference a)).stacks i).length ≤ W)
    (occurrence qi K count B width : ℕ)
    (ctx : Marked.Wide.BranchContext Residual.command (Marked.Wide.maskCopied (prepared p.out))
      (ProtectedWork (Carried.reference a)) count B width)
    (hz : (prepared p.out).stacks 333=[])
    (hs : ctx.stepBudget ≤ residualCap (ordinaryCap p occurrence qi) K)
    (hwidth : ctx.stepWidth ≤ ordinaryCap p occurrence qi)
    (href : ctx.referenceBound ≤ ordinaryCap p occurrence qi) :
    ∃n b, n ≤ queryCap (ordinaryCap p occurrence qi) K
        (CostAssembly.assembledWork k (ambient q) (resources q k occurrence qi hg p.firstWord p.remainingWords)) ∧
      Eval (marked k) n a b ∧ Marked.Wide.workspace b=Marked.Wide.workspace a ∧
      b.stacks 320=a.stacks 320 ∧ b.stacks 322=a.stacks 322 ∧
      BinaryArithmetic.toNat (b.stacks 323)=count ∧ (b.stacks 323).length ≤ width ∧
      b.regs 16=false ∧ b.regs 17=true ∧ b.regs 18=false ∧
      b.stacks 321=[] ∧ b.stacks 324=[] := by
  obtain ⟨ctx'⟩ := capped_context ctx (ordinaryCap p occurrence qi) K hs href
  obtain ⟨n,b,hn,he,hrest⟩ := Carried.marked_from_masked_preparation q k a hg W V L p hc hw
    count _ width ctx'
  have hsum := setup_le_ordinary p occurrence qi
  obtain ⟨hm,hN⟩ := copied_mask_le p occurrence qi hw hz
  have hbudget := complete_measured_le p (Marked.Wide.maskCopied (prepared p.out))
    (ordinaryCap p occurrence qi) K _ ctx.stepWidth (ordinaryCap p occurrence qi)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (prepared_width_le p occurrence qi hw 338) hm hwidth (by rfl) hN
  have hr := hw 321
  rw [markedInput_frame _ 321 (by decide) (by decide) (by decide),
    Carried.reference_visible a 321 (by decide)] at hr
  refine ⟨n,b,?_,he,hrest⟩
  exact hn.trans ((by omega : 10*(a.stacks 321).length+10+preparationBudget p _ ≤
    10*ordinaryCap p occurrence qi+10+preparationBudget p _).trans hbudget)

 theorem accepted_measured (q : LeafQueryFrontend.Query) (k : ℕ) (a : Data)
    (hg : Guard (q.input k)) (W V L : ℕ)
    (p : Preparation q k (unmarkedInput (Carried.reference a)) hg W V L)
    (hc : CleanWork a) (hw : ∀i,((unmarkedInput (Carried.reference a)).stacks i).length ≤ W)
    (occurrence qi K count B width : ℕ)
    (ctx : Marked.Wide.BranchContext Residual.command (Marked.Wide.maskCopied (prepared p.out))
      (ProtectedWork (Carried.reference a)) count B width)
    (hz : (prepared p.out).stacks 333=[])
    (hs : ctx.stepBudget ≤ residualCap (ordinaryCap p occurrence qi) K)
    (hwidth : ctx.stepWidth ≤ ordinaryCap p occurrence qi)
    (href : ctx.referenceBound ≤ ordinaryCap p occurrence qi) :
    ∃n b, n ≤ queryCap (ordinaryCap p occurrence qi) K
        (CostAssembly.assembledWork k (ambient q) (resources q k occurrence qi hg p.firstWord p.remainingWords)) ∧
      Eval (accepted k) n a b ∧ Marked.Wide.workspace b=Marked.Wide.workspace a ∧
      b.stacks 320=a.stacks 320 ∧ b.stacks 322=a.stacks 322 ∧
      BinaryArithmetic.toNat (b.stacks 323)=count ∧ (b.stacks 323).length ≤ width ∧
      b.regs 16=false ∧ b.regs 17=true ∧ b.regs 18=false ∧
      b.stacks 321=[] ∧ b.stacks 324=[] := by
  obtain ⟨ctx'⟩ := capped_context ctx (ordinaryCap p occurrence qi) K hs href
  obtain ⟨n,b,hn,he,hrest⟩ := Carried.accepted_from_masked_preparation q k a hg W V L p hc hw
    count _ width ctx'
  have hsum := setup_le_ordinary p occurrence qi
  obtain ⟨hm,hN⟩ := copied_mask_le p occurrence qi hw hz
  have hbudget := complete_measured_le p (Marked.Wide.maskCopied (prepared p.out))
    (ordinaryCap p occurrence qi) K _ ctx.stepWidth (ordinaryCap p occurrence qi)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (prepared_width_le p occurrence qi hw 338) hm hwidth (by rfl) hN
  exact ⟨n,b,hn.trans ((by omega : 3+preparationBudget p _ ≤
    10*ordinaryCap p occurrence qi+10+preparationBudget p _).trans hbudget),he,hrest⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost

end OAI.Algorithms
