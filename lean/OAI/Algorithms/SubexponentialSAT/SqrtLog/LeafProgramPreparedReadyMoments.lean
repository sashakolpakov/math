import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyFacts
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsAssemblyProgramReachableModel

namespace OAI.Algorithms

/-! Source and factor masters survive every actual nested moment-loop state.
Only ports160--178 vary in those pure loop-state specifications. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open MomentsAssembly MomentsProgram MomentsAssembly.Relational
attribute [local simp] Fin.coe_ofNat_eq_mod

def MomentFrame (base high : Fin 768 → List Bool) : Prop :=
  ∀ i, i.val < 160 ∨ 178 < i.val → high i=base i

 theorem NodeFacts.frame {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {base high : Fin 768 → List Bool} (h : NodeFacts q base) (hf : MomentFrame base high) :
    NodeFacts q high := by
  have hs : SourceMasters q.p q.ps q.packing (FactorReady.baseData high) := by
    constructor
    · exact (hf _ (by decide)).trans h.source.colors
    · exact (hf _ (by decide)).trans h.source.nodes
    · exact (hf _ (by decide)).trans h.source.typeWidth
    · exact (hf _ (by decide)).trans h.source.positive
    · exact (hf _ (by decide)).trans h.source.negative
    · exact (hf _ (by decide)).trans h.source.scalarWidth
    · exact (hf _ (by decide)).trans h.source.power
    · exact h.source.powerNegative
    · exact (hf _ (by decide)).trans h.source.radius
    · exact (hf _ (by decide)).trans h.source.offset
    · exact (hf _ (by decide)).trans h.source.metadata
    · exact (hf _ (by decide)).trans h.source.plans
    · exact (hf _ (by decide)).trans h.source.inverses
    · exact (hf _ (by decide)).trans h.source.negatives
    · exact (hf _ (by decide)).trans h.source.differences
    · exact (hf _ (by decide)).trans h.source.ringWidth
    · exact (hf _ (by decide)).trans h.source.rowWidth
    · exact (hf _ (by decide)).trans h.source.zero
    · exact (hf _ (by decide)).trans h.source.one
    · exact (hf _ (by decide)).trans h.source.minusOne
    · exact (hf _ (by decide)).trans h.source.inverseDenominator
  constructor
  · exact hs
  · intro i hi
    rw [hf i (by rcases hi with hi|hi|hi <;> omega)]
    exact h.clean i hi
  · exact (hf _ (by decide)).trans h.modulus
  · exact (hf _ (by decide)).trans h.width
  · exact (hf _ (by decide)).trans h.scalarZero
  · exact (hf _ (by decide)).trans h.table
  · exact (hf _ (by decide)).trans h.degree
  · exact (hf _ (by decide)).trans h.theta
  · exact (hf _ (by decide)).trans h.target
  · exact (hf _ (by decide)).trans h.ambient
  · rw [hf 703 (by decide)]; exact h.highLength
  · exact (hf _ (by decide)).trans h.rows
  · exact (hf _ (by decide)).trans h.clauses
  · exact (hf _ (by decide)).trans h.count
  · exact (hf _ (by decide)).trans h.mark
  · exact (hf _ (by decide)).trans h.flag
  · rw [hf 708 (by decide)]; exact h.hashWidth
  · rw [hf 707 (by decide)]; exact h.hashModulus
  · exact (hf _ (by decide)).trans h.one
  · exact (hf _ (by decide)).trans h.minus
  · exact (hf _ (by decide)).trans h.tape
  · rw [hf 88 (by decide)]; exact h.shape

 theorem reachable_master_frame {n B d : ℕ} (vars : Finset (Fin n)) (u J : ℕ)
    (base : Fin 768 → List Bool) (ss : List (Finset (Fin n))) (bs : List BucketInput) :
    Reachable.BucketFrames B d vars u J (MomentFrame base) base ss bs := by
  intro seed hseed source hsource b hb tail htail seed' hseed' source' hsource' s hs tail' htail'
    h hh headTail hheadTail assignmentTail hat x hx i hi
  have hn : i≠160 ∧ i≠161 ∧ i≠162 ∧ i≠163 ∧ i≠166 ∧ i≠168 ∧
      i≠170 ∧ i≠174 ∧ i≠175 ∧ i≠176 ∧ i≠177 ∧ i≠178 := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
      intro he <;> subst i <;> norm_num at hi
  simp only [bucketStream,bucketHigh,bucketHigh1,bucketHigh2,bucketHigh3,
    supportStream,supportHigh,headHigh,headHigh1,headHigh2,headHigh3,
    Function.update_of_ne hn.1,Function.update_of_ne hn.2.1,
    Function.update_of_ne hn.2.2.1,Function.update_of_ne hn.2.2.2.1,
    Function.update_of_ne hn.2.2.2.2.1,Function.update_of_ne hn.2.2.2.2.2.1,
    Function.update_of_ne hn.2.2.2.2.2.2.1,Function.update_of_ne hn.2.2.2.2.2.2.2.1,
    Function.update_of_ne hn.2.2.2.2.2.2.2.2.1,Function.update_of_ne hn.2.2.2.2.2.2.2.2.2.1,
    Function.update_of_ne hn.2.2.2.2.2.2.2.2.2.2.1,Function.update_of_ne hn.2.2.2.2.2.2.2.2.2.2.2]

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
