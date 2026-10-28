import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteResidualProduct
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteWeights

namespace OAI.Algorithms

/-! The exact stored bucket fibers feed the polynomial head-moment theorem.
No replacement raw dictionaries or assignment encodings are chosen. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open MomentsAssembly MomentsAssembly.Relational _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree
open BucketTupleProgram.Concrete

variable {r Q n d : ℕ}

section Bucket
variable (q : Factor.Spec r Q n d) (H : Finset (Fin n)) (high : H → Bool)
    (mask bits : List Bool) (headIds : List Bool → List ℕ)
    (head : ResidualEmbedding.Free H → Fin r)
    {D : ℕ} {C : ℕ → ℕ → ℤ} {tables : Fin r → BucketTupleProgram.HeadTable}
    (s : ∀ g,HeadSemantics H head g D C (tables g))
    (y : ∀ g,Moments.LabelValue (fun g=>(s g).label) g)

def bucketFactor (g : Fin r) (a : Moments.LabelBucket (fun g=>(s g).label) g (y g)) :
    Jet (ResidualEmbedding.Free H) (q.p.model.O q.p.t) :=
  residualProduct q H high mask bits headIds
    ⟨[],((s g).input (y g)).mask,((s g).input (y g)).context,(familyInput s y).context⟩
    ((s g).encode a.val)

theorem bucketFactor_admissible (g : Fin r)
    (a : Moments.LabelBucket (fun g=>(s g).label) g (y g)) :
    Admissible (bucketFactor q H high mask bits headIds head s y g a) :=
  residualProduct_admissible q H high mask bits headIds _ _

theorem bucket_semantic
    (hmask : ∀ v : Fin n,mask.getD v.val false=decide (v∈H))
    (hbits : ∀ v : H,bits.getD v.val.val false=high v)
    (hzero : ∀ id j (v : Fin n),v∈H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v=0)
    (hm : ∀ g,(tables g).mask=List.ofFn (headMask H head g))
    (support : Finset (Fin n)) (g : Fin r)
    (a : Moments.LabelBucket (fun g=>(s g).label) g (y g)) :
    AssignmentConcrete.semantic q mask bits headIds
      ⟨encodeMask support,((s g).input (y g)).mask,((s g).input (y g)).context,(familyInput s y).context⟩
      ((s g).encode a.val) =
    Moments.ringScalar (nativeWeight H head support g a.val)*
      ResidualEmbedding.jet (ResidualEmbedding.inclusion H)
        (bucketFactor q H high mask bits headIds head s y g a) := by
  unfold AssignmentConcrete.semantic
  rw [localProduct_embedding q H high mask bits hmask hbits hzero]
  congr 1
  · rw [(s g).encode_eq a.val,(s g).input_mask (y g),hm g]
    rfl

theorem bucket_moments
    (hmask : ∀ v : Fin n,mask.getD v.val false=decide (v∈H))
    (hbits : ∀ v : H,bits.getD v.val.val false=high v)
    (hzero : ∀ id j (v : Fin n),v∈H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v=0)
    (hm : ∀ g,(tables g).mask=List.ofFn (headMask H head g))
    (ss : List (Finset (Fin n))) (hs : ss.Nodup)
    (fs : Finset (Finset (ResidualEmbedding.Free H)))
    (hmem : ∀ a,a.map (ResidualEmbedding.inclusion H)∈ss ↔ a∈fs)
    (hM : ∀ a : Finset (ResidualEmbedding.Free H),a.card < q.J → a∈fs) :
    semanticReadout q.u q.J (bucketDenotation q.u q.J
      (AssignmentConcrete.semantic q mask bits headIds) ss (familyInput s y)) =
    ∑ a : ∀ g,Moments.LabelBucket (fun g=>(s g).label) g (y g),
      Truncation.trunc q.J (Moments.sumUCoeff q.u
        (Moments.jetEval (Squarefree.boolValue (Moments.assemble head (fun g=>(a g).val)))
          (Squarefree.boolValue_idempotent _) (∏ g,bucketFactor q H high mask bits headIds head s y g (a g)))) := by
  let xs (g : Fin r) := ((s g).fiber_enum (y g)).choose
  have hxn (g : Fin r) : (xs g).Nodup := ((s g).fiber_enum (y g)).choose_spec.1
  have hxc (g : Fin r) : (xs g).toFinset=Finset.univ := by
    ext a
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    exact ((s g).fiber_enum (y g)).choose_spec.2.1 a
  have hxa (g : Fin r) : ((s g).input (y g)).assignments=(xs g).map (fun a=>(s g).encode a.val) :=
    ((s g).fiber_enum (y g)).choose_spec.2.2.symm
  apply bucket_polynomial_embedded q.u q.J (AssignmentConcrete.semantic q mask bits headIds)
    ss hs (familyInput s y).context (familyInput s y).heads (ResidualEmbedding.inclusion H)
    fs hmem hM (bucketFactor q H high mask bits headIds head s y)
    (bucketFactor_admissible q H high mask bits headIds head s y)
    (fun support g a=>nativeWeight H head support g a.val)
    (fun support g a=>Moments.localBoolWeight head ⟨support⟩ g a.val)
    (fun support g a=>nativeWeight_map H head support g a.val)
  · intro support hsupport
    have hheads : (familyInput s y).heads=(List.finRange r).map (fun g=>(s g).input (y g)) := by
      exact List.ofFn_eq_map
    rw [hheads]
    exact head_product_embedded (AssignmentConcrete.semantic q mask bits headIds)
      (List.finRange r) (List.nodup_finRange r) (by ext; simp) xs hxn hxc
      (fun g=>(s g).input (y g)) (fun g a=>(s g).encode a.val) hxa
      (ResidualEmbedding.inclusion H) (bucketFactor q H high mask bits headIds head s y)
      (fun g a=>nativeWeight H head support g a.val) support (familyInput s y).context
      (bucket_semantic q H high mask bits headIds head s y hmask hbits hzero hm support)
  · intro support a
    rw [Moments.boolWeight_partition head ⟨support⟩ (fun g=>(a g).val)]
    simp only [Moments.jetConstant,map_prod]

end Bucket
end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
