import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteBucketMoments
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentConcreteProduct
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyRelSemanticsLoops
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteSpecTarget

namespace OAI.Algorithms

/-! Actual attained-fiber products evaluate to the shared source query.
The premises are incidence lookup and the native head-ID partition. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open Polynomial _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open LayoutProgram PerturbationAssembly MomentsAssembly
open BucketTupleProgram.Concrete

variable {r Q n d : ℕ}

section Query
variable (q : Factor.Spec r Q n d) (hu : q.u=q.p.t)
    (owner : Fin q.ps.length → Fin n) (howner : ∀ i,(q.ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r) (hhead : ∀ i t,(q.packing.label i).head t=head t (owner i))
    (H : Finset (Fin n)) (hlow : ∀ i,owner i∉H) (high : H → Bool) (node : Fin Q)
    {tables : Fin r → BucketTupleProgram.HeadTable}
    (s : ∀ g,HeadSemantics H (fun v=>head node v.val) g q.ps.length
      (LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R node) (tables g))
    (y : ∀ g,Moments.LabelValue (fun g=>(s g).label) g)
    (hm : ∀ g,(tables g).mask=List.ofFn (headMask H (fun v=>head node v.val) g))
    (htheta : q.p.ops.decode q.theta=q.p.model.node q.p.t Q q.p.ht q.p.hfield node)
    (mask bits : List Bool)
    (hmask : ∀ v : Fin n,mask.getD v.val false=decide (v∈H))
    (hbits : ∀ v : H,bits.getD v.val.val false=high v)
    (headIds : List Bool → List ℕ) (ids : List ℕ) (hn : ids.Nodup) (color : ℕ → Fin r)
    (hids : ∀ g,headIds ((s g).input (y g)).context=ids.filter (fun id=>color id=g))
    (hslot : ∀ f j (hp : (j,n+f)∈q.ps),
      (q.packing.label (planIndex q.ps n f j hp)).slot 0 node=color f)
    (hhash : ∀ id∈ids,∀ hi:id < (AssignmentConcrete.weightedHashes q).length,
      ∀ w∈(AssignmentConcrete.weightedHashes q)[id],∀ l∈w.literals,
        l.variable∉H → (l.variable.val,n+id)∈q.ps)
    (hmark : q.marked=true → (AssignmentConcrete.weightedHashes q).length∈ids →
      ∀ l∈q.markedClause,l.variable∉H → (l.variable.val,n+(AssignmentConcrete.weightedHashes q).length)∈q.ps)
    (hh : ∀ i < (AssignmentConcrete.weightedHashes q).length,i∈ids)
    (hmid : q.marked=true → (AssignmentConcrete.weightedHashes q).length∈ids)

include hu howner hhead hlow hm htheta hmask hbits hn hids hslot hhash hmark hh hmid in
 theorem bucket_product_query
    (a : ∀ g,Moments.LabelBucket (fun g=>(s g).label) g (y g)) :
    Truncation.trunc q.J (Moments.sumUCoeff q.u
      (Moments.jetEval (Squarefree.boolValue (Moments.assemble (fun v=>head node v.val) (fun g=>(a g).val)))
        (Squarefree.boolValue_idempotent _) (∏ g,bucketFactor q H high mask bits headIds
          (fun v=>head node v.val) s y g (a g)))) =
    Truncation.trunc q.J ((NodeSemantics.queryPolynomial q.p.t
      (NodeSemantics.codeDigits q.ctx (q.p.model.base q.p.t) q.code) (decodedHashes q) q.marked q.markedClause
      (NodeSemantics.branchPath H high (completedRows q.p q.ps q.packing H)
        (Moments.assemble (fun v=>head node v.val) (fun g=>(a g).val)))).comp
      (X+C (q.p.ops.decode q.theta))) := by
  let ctx (g : Fin r) : AssignmentContext :=
    ⟨[],((s g).input (y g)).mask,((s g).input (y g)).context,(familyInput s y).context⟩
  let jets (g : Fin r) := AssignmentConcrete.assignmentJets q mask bits (ctx g) ((s g).encode (a g).val)
  let D (g : Fin r) := canonical q.u q.J
    (AssignmentConcrete.localProduct q mask bits headIds (ctx g) ((s g).encode (a g).val))
  have hz : ∀ id j (v : Fin n),v∈H → fixedSourceRow q.p q.ps q.packing n id j v=0 :=
    fixedSourceRow_high_zero q.p q.ps q.packing owner howner H hlow
  have he (g : Fin r) : D g=ResidualEmbedding.jet (ResidualEmbedding.inclusion H)
      (bucketFactor q H high mask bits headIds (fun v=>head node v.val) s y g (a g)) :=
    localProduct_embedding q H high mask bits hmask hbits hz headIds _ _
  rw [←NodeSemantics.embedded_product_readout q.u q.J H high D _ he]
  apply AssignmentConcrete.colored_products_query_scoped q.ctx hu
    (q.p.model.base q.p.t) (RingBasis.basis (q.p.model.F q.p.t)) q.code ids hn color jets D
    (NodeSemantics.branchPath H high (completedRows q.p q.ps q.packing H)
      (Moments.assemble (fun v=>head node v.val) (fun g=>(a g).val)))
    (q.p.ops.decode q.theta) (Squarefree.boolValue (HighIncidence.glue H high
      (Moments.assemble (fun v=>head node v.val) (fun g=>(a g).val))))
    (Squarefree.boolValue_idempotent _) (AssignmentConcrete.weightedHashes q) q.marked q.markedClause
  · intro g id hid hcolor hi w hw l hl
    exact merged_factorJet_eval q.p q.ps q.packing owner howner head hhead H hlow high node
      s y a hm q.theta htheta mask bits hmask hbits [] id l.variable g
      (hhash id hid hi w hw l hl) (fun hj=>(hslot id l.variable.val _).trans hcolor)
  · intro g hmarked hid hcolor l hl
    exact merged_factorJet_eval q.p q.ps q.packing owner howner head hhead H hlow high node
      s y a hm q.theta htheta mask bits hmask hbits [] _ l.variable g
      (hmark hmarked hid l hl) (fun hj=>(hslot _ l.variable.val _).trans hcolor)
  · exact hh
  · exact hmid
  · intro g
    dsimp [D,AssignmentConcrete.localProduct,ctx]
    rw [hids g]
    rfl

include hu howner hhead hlow hm htheta hmask hbits hn hids hslot hhash hmark hh hmid in
 theorem bucket_query (ss : List (Finset (Fin n))) (hs : ss.Nodup)
    (hsmall : ∀ S,S∈ss ↔ S.card < q.J) :
    semanticReadout q.u q.J (Relational.bucketDenotation q.u q.J
      (AssignmentConcrete.semantic q mask bits headIds) ss (familyInput s y)) =
    ∑ a : ∀ g,Moments.LabelBucket (fun g=>(s g).label) g (y g),
      Truncation.trunc q.J ((NodeSemantics.queryPolynomial q.p.t
        (NodeSemantics.codeDigits q.ctx (q.p.model.base q.p.t) q.code) (decodedHashes q) q.marked q.markedClause
        (NodeSemantics.branchPath H high (completedRows q.p q.ps q.packing H)
          (Moments.assemble (fun v=>head node v.val) (fun g=>(a g).val)))).comp
        (X+C (q.p.ops.decode q.theta))) := by
  let fs : Finset (Finset (ResidualEmbedding.Free H)) := Finset.univ.filter (fun S=>S.card < q.J)
  have hmem : ∀ S,S.map (ResidualEmbedding.inclusion H)∈ss ↔ S∈fs := by
    intro S
    rw [hsmall,Finset.card_map]
    simp only [fs,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [bucket_moments q H high mask bits headIds (fun v=>head node v.val) s y hmask hbits
    (fixedSourceRow_high_zero q.p q.ps q.packing owner howner H hlow) hm ss hs fs hmem
    (by intro S hS; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hS⟩)]
  apply Finset.sum_congr rfl
  intro a _
  exact bucket_product_query q hu owner howner head hhead H hlow high node s y hm htheta
    mask bits hmask hbits headIds ids hn color hids hslot hhash hmark hh hmid a

include hu howner hhead hlow hm htheta hmask hbits hn hslot hhash hmark hh hmid in
 theorem buckets_specTarget
    (hids' : ∀ y' : ∀ g,Moments.LabelValue (fun g=>(s g).label) g,
      ∀ g,headIds ((s g).input (y' g)).context=ids.filter (fun id=>color id=g))
    (ss : List (Finset (Fin n))) (hs : ss.Nodup)
    (hsmall : ∀ S,S∈ss ↔ S.card < q.J)
    (ys : List (∀ g,Moments.LabelValue (fun g=>(s g).label) g))
    (hyn : ys.Nodup) (hyc : ys.toFinset=Finset.univ)
    (zero one : RingProgram.Code (Word (baseWidth 3 q.p.t)) d)
    (hz : q.p.ops.decode zero=0) (ho : q.p.ops.decode one=1)
    (entries : Relational.Raw 3 q.p.t (n:=n) (d:=d))
    (hr : Relational.BucketsRel 3 q.p.t q.p.modulus q.p.cache q.ctx.table q.u q.J
      (AssignmentConcrete.relation q mask bits headIds zero one) ss q.one
      (ys.map (familyInput s)) [] entries) :
    output 3 q.p.t q.p.modulus q.p.cache (q.p.model.base q.p.t)
      (RingBasis.basis (q.p.model.F q.p.t)) q.u q.J entries =
      JetCRT.jet (q.p.ops.decode q.theta) q.J (specTarget q H high) := by
  rw [Relational.buckets_output 3 q.p.t q.p.modulus q.p.cache
    (q.p.model.base q.p.t) (RingBasis.basis (q.p.model.F q.p.t)) q.ctx.table
    (Factor.Semantics.context_table_correct q.p q.u q.J q.width q.widthLength)
    q.u q.J (AssignmentConcrete.relation q mask bits headIds zero one)
    (AssignmentConcrete.semantic q mask bits headIds)
    (AssignmentConcrete.contribution_denote q mask bits headIds zero one hz ho)
    hr (by simp [Sparse.keys]) q.oneValue,output_nil,add_zero]
  simp only [List.map_map,Function.comp_def]
  have he (y' : ∀ g,Moments.LabelValue (fun g=>(s g).label) g) :=
    bucket_query q hu owner howner head hhead H hlow high node s y' hm htheta
      mask bits hmask hbits headIds ids hn color (hids' y') hslot hhash hmark hh hmid ss hs hsmall
  simp only [he]
  rw [←List.sum_toFinset _ hyn,hyc]
  rw [←Moments.sum_boolean_actual_buckets (fun v : ResidualEmbedding.Free H=>head node v.val) (fun g=>(s g).label)
    (fun x=>Truncation.trunc q.J ((NodeSemantics.queryPolynomial q.p.t
      (NodeSemantics.codeDigits q.ctx (q.p.model.base q.p.t) q.code) (decodedHashes q) q.marked q.markedClause
      (NodeSemantics.branchPath H high (completedRows q.p q.ps q.packing H) x)).comp
      (X+C (q.p.ops.decode q.theta))))]
  exact NodeSemantics.sum_query_jets H q.p.t q.J
    (NodeSemantics.codeDigits q.ctx (q.p.model.base q.p.t) q.code) (decodedHashes q)
    q.marked q.markedClause
    (NodeSemantics.branchPath H high (completedRows q.p q.ps q.packing H))
    (q.p.ops.decode q.theta)

end Query
end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
