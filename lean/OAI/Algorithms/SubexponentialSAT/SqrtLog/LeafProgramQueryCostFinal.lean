import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostNative
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostPolynomial

namespace OAI.Algorithms

/-! Complete actual marked/final query cost, with original source padding and
assembled work kept separate. The residual contract is supplied by the concrete
prepared-branch proof, with the explicit node polynomial as its per-node cap. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram ProducedQueryResources

 theorem prepared_333 {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Preparation q k a hg W V L)
    (hz : a.stacks 333=[]) : (prepared p.out).stacks 333=[] := by
  have hf := p.frontOutput.frame 333 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by intro j; fin_cases j <;> decide)
  have hp := p.packingFrame 333 (by decide) (by decide) (by decide)
  have ha := p.arithmeticOutput.collectorFrame 333 (by decide) (by decide)
  exact (Count.Prepare.output_high_frame (Samples.prepared p.out) 333 (by decide) (by decide)).trans
    ((Samples.prepared_frame p.out 333 (by decide) (by decide)).trans (ha.trans (hp.trans (hf.trans hz))))

 theorem marked_polynomial (k CK x y z : ℕ) : ∃ C e : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (a : Data) (hg : Guard (q.input k))
      (V L : ℕ) (p : Preparation q k (markedInput (Carried.reference a)) hg (Carried.markedWidth a) V L)
      (occurrence qi count B width : ℕ)
      (ctx : Marked.Wide.BranchContext Residual.command (Marked.Wide.maskCopied (prepared p.out))
        (ProtectedWork (Carried.reference a)) count B width),
    q.Valid → CleanWork a → Sources q a → q.mark.isSome=true → a.stacks 321=q.index.reverse →
    a.stacks 323=[] → (∀i : Fin 768,744 ≤ i.val → a.stacks i=[]) →
    2 ≤ ambient q → SmallInputs q k (ambient q) →
    V=modelValueCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) →
    L=modelLengthCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) →
    ctx.stepBudget ≤ residualCap (ordinaryCap p occurrence qi) (nodeCap p occurrence qi CK x y z) →
    ctx.stepWidth ≤ ordinaryCap p occurrence qi → ctx.referenceBound ≤ ordinaryCap p occurrence qi →
    ∃n b, n ≤ C*(Carried.sourceBytes a+1)^e*(ambient q+1)^((ordinaryExponent+1)*e)*
        (CostAssembly.assembledWork k (ambient q) (resources q k occurrence qi hg p.firstWord p.remainingWords)+1)^e ∧
      Eval (marked k) n a b ∧ Marked.Wide.workspace b=Marked.Wide.workspace a ∧
      b.stacks 320=a.stacks 320 ∧ b.stacks 322=a.stacks 322 ∧
      BinaryArithmetic.toNat (b.stacks 323)=count ∧ (b.stacks 323).length ≤ width ∧
      b.regs 16=false ∧ b.regs 17=true ∧ b.regs 18=false ∧ b.stacks 321=[] ∧ b.stacks 324=[] := by
  obtain ⟨C,e,hpoly⟩ := queryCap_produced_polynomial k CK x y z
  refine ⟨C*11^e,e,?_⟩
  intro q a hg V L p occurrence qi count B width ctx hv hc hsrc hm href0 h323 hhigh hn hsmall hV hL hstep hwidth href
  have hw := Carried.marked_source_width a hc h323 hhigh
  obtain ⟨he,hr,ho,hsp⟩ := marked_entry q (Carried.reference a) (Carried.reference_clean a hc)
    (Carried.sources_reference q a hsrc) hm ((Carried.reference_visible a 321 (by decide)).trans href0)
  have hz : (markedInput (Carried.reference a)).stacks 333=[] :=
    (markedInput_frame _ 333 (by decide) (by decide) (by decide)).trans ((Carried.reference_visible a 333 (by decide)).trans (hc _ (by decide) (by decide)))
  obtain ⟨n,b,ht,he,hrest⟩ := marked_measured q k a hg (Carried.markedWidth a) V L p hc hw
    occurrence qi (nodeCap p occurrence qi CK x y z) count B width ctx (prepared_333 p hz) hstep hwidth href
  have hp := hpoly q occurrence qi (markedInput (Carried.reference a)) hg (Carried.markedWidth a) V L p
    hv hr hw hn hsmall hV hL
  exact ⟨n,b,ht.trans (hp.trans (source_padding_absorb C e (ambient q) _
    (Carried.markedWidth a) (Carried.sourceBytes a) (marked_width_le a))),he,hrest⟩

 theorem accepted_polynomial (k CK x y z : ℕ) : ∃ C e : ℕ,
    ∀ (q : LeafQueryFrontend.Query) (a : Data) (hg : Guard (q.input k))
      (V L : ℕ) (p : Preparation q k (unmarkedInput (Carried.reference a)) hg (Carried.acceptedWidth a) V L)
      (occurrence qi count B width : ℕ)
      (ctx : Marked.Wide.BranchContext Residual.command (Marked.Wide.maskCopied (prepared p.out))
        (ProtectedWork (Carried.reference a)) count B width),
    q.Valid → CleanWork a → Sources q a → q.mark=none → q.index=[false] →
    a.stacks 323=[] → (∀i : Fin 768,744 ≤ i.val → a.stacks i=[]) →
    2 ≤ ambient q → SmallInputs q k (ambient q) →
    V=modelValueCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) →
    L=modelLengthCap (Circuit.result Serialization.code (Execute.guardedModel (q.input k) p.lengths)) →
    ctx.stepBudget ≤ residualCap (ordinaryCap p occurrence qi) (nodeCap p occurrence qi CK x y z) →
    ctx.stepWidth ≤ ordinaryCap p occurrence qi → ctx.referenceBound ≤ ordinaryCap p occurrence qi →
    ∃n b, n ≤ C*(Carried.sourceBytes a+1)^e*(ambient q+1)^((ordinaryExponent+1)*e)*
        (CostAssembly.assembledWork k (ambient q) (resources q k occurrence qi hg p.firstWord p.remainingWords)+1)^e ∧
      Eval (accepted k) n a b ∧ Marked.Wide.workspace b=Marked.Wide.workspace a ∧
      b.stacks 320=a.stacks 320 ∧ b.stacks 322=a.stacks 322 ∧
      BinaryArithmetic.toNat (b.stacks 323)=count ∧ (b.stacks 323).length ≤ width ∧
      b.regs 16=false ∧ b.regs 17=true ∧ b.regs 18=false ∧ b.stacks 321=[] ∧ b.stacks 324=[] := by
  obtain ⟨C,e,hpoly⟩ := queryCap_produced_polynomial k CK x y z
  refine ⟨C*11^e,e,?_⟩
  intro q a hg V L p occurrence qi count B width ctx hv hc hsrc hm hindex h323 hhigh hn hsmall hV hL hstep hwidth href
  have hw := Carried.accepted_source_width a hc h323 hhigh
  obtain ⟨he,hr,ho,hsp⟩ := accepted_entry q (Carried.reference a) (Carried.reference_clean a hc)
    (Carried.sources_reference q a hsrc) hm hindex
  have hz : (unmarkedInput (Carried.reference a)).stacks 333=[] :=
    (unmarkedInput_frame _ 333 (by decide) (by decide)).trans ((Carried.reference_visible a 333 (by decide)).trans (hc _ (by decide) (by decide)))
  obtain ⟨n,b,ht,he,hrest⟩ := accepted_measured q k a hg (Carried.acceptedWidth a) V L p hc hw
    occurrence qi (nodeCap p occurrence qi CK x y z) count B width ctx (prepared_333 p hz) hstep hwidth href
  have hp := hpoly q occurrence qi (unmarkedInput (Carried.reference a)) hg (Carried.acceptedWidth a) V L p
    hv hr hw hn hsmall hV hL
  exact ⟨n,b,ht.trans (hp.trans (source_padding_absorb C e (ambient q) _
    (Carried.acceptedWidth a) (Carried.sourceBytes a) (accepted_width_le a))),he,hrest⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Query.Cost

end OAI.Algorithms
