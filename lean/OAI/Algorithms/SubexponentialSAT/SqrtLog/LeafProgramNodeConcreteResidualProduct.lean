import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteNativeJets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentConcreteEmbedding

namespace OAI.Algorithms

/-! Actual head polynomials live in the free-variable algebra. Each factor
and multiplication retains the same U and T cutoffs as the native program. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsAssembly _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree

variable {r Q n d : ℕ}

def assignmentFreeJets (q : Factor.Spec r Q n d) (H : Finset (Fin n)) (high : H → Bool)
    (mask bits : List Bool) (c : AssignmentContext) (x : List Bool) :=
  residualJet q.p q.ps q.packing H high q.theta (FactorLoop.assignmentReference mask bits c x)

def residualProduct (q : Factor.Spec r Q n d) (H : Finset (Fin n)) (high : H → Bool)
    (mask bits : List Bool) (headIds : List Bool → List ℕ) (c : AssignmentContext) (x : List Bool) :
    Jet (ResidualEmbedding.Free H) (q.p.model.O q.p.t) :=
  canonical q.u q.J (((headIds c.head).map
    (AssignmentConcrete.residualValue q.ctx (q.p.model.base q.p.t)
      (RingBasis.basis (q.p.model.F q.p.t)) q.code (assignmentFreeJets q H high mask bits c x)
      (AssignmentConcrete.weightedHashes q) q.marked q.markedClause)).prod)

theorem residualJet_admissible (q : Factor.Spec r Q n d) (H : Finset (Fin n)) (high : H → Bool)
    (state : Fin 768 → List Bool) (id : ℕ) (v : Fin n) :
    Admissible (residualJet q.p q.ps q.packing H high q.theta state id v) := by
  unfold residualJet
  split
  · exact AssignmentConcrete.admissible_ringScalar _
  · exact Moments.incidenceJet_admissible _ _ _

theorem residualProduct_admissible (q : Factor.Spec r Q n d) (H : Finset (Fin n)) (high : H → Bool)
    (mask bits : List Bool) (headIds : List Bool → List ℕ) (c : AssignmentContext) (x : List Bool) :
    Admissible (residualProduct q H high mask bits headIds c x) :=
  AssignmentConcrete.residual_product_admissible q.ctx (q.p.model.base q.p.t)
    (RingBasis.basis (q.p.model.F q.p.t)) q.code _
    (residualJet_admissible q H high _) _ _ _ _

theorem localProduct_embedding (q : Factor.Spec r Q n d) (H : Finset (Fin n)) (high : H → Bool)
    (mask bits : List Bool)
    (hmask : ∀ v : Fin n,mask.getD v.val false=decide (v∈H))
    (hbits : ∀ v : H,bits.getD v.val.val false=high v)
    (hzero : ∀ id j (v : Fin n),v∈H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v=0)
    (headIds : List Bool → List ℕ) (c : AssignmentContext) (x : List Bool) :
    canonical q.u q.J (AssignmentConcrete.localProduct q mask bits headIds c x) =
      ResidualEmbedding.jet (ResidualEmbedding.inclusion H)
        (residualProduct q H high mask bits headIds c x) := by
  apply AssignmentConcrete.canonical_product_embedding (ResidualEmbedding.inclusion H) q.ctx
    (q.p.model.base q.p.t) (RingBasis.basis (q.p.model.F q.p.t)) q.code
    (assignmentFreeJets q H high mask bits c x) (AssignmentConcrete.assignmentJets q mask bits c x)
    _ (AssignmentConcrete.weightedHashes q) q.marked q.markedClause (headIds c.head)
  intro id v
  apply factorJet_embedding q.p q.ps q.packing H high q.theta _ id v
  · simpa [FactorLoop.assignmentReference] using hmask v
  · intro hv
    simpa [FactorLoop.assignmentReference] using hbits ⟨v,hv⟩
  · exact hzero id v.val

theorem residualProduct_support (q : Factor.Spec r Q n d) (H : Finset (Fin n)) (high : H → Bool)
    (mask bits : List Bool) (headIds : List Bool → List ℕ)
    (support support' headMask head bucket x : List Bool) :
    residualProduct q H high mask bits headIds ⟨support,headMask,head,bucket⟩ x =
      residualProduct q H high mask bits headIds ⟨support',headMask,head,bucket⟩ x := rfl

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
