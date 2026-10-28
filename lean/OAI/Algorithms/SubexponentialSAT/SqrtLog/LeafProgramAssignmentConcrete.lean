import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentSemantics

namespace OAI.Algorithms

/-! The relational, actually executed assignment fold has the same value as
the selected-factor expression used by the node proof.  This bridge chooses
no raw representative and retains the shared U and T truncations. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

open SubexponentialSAT SubexpLiftRing SubexpQuarticRing MomentsProgram MomentsAssembly
open HashCircuitProgram HashCircuitProgram.Native
open scoped BigOperators

variable {r Q n d : ℕ}

def weightedHashes (q : Factor.Spec r Q n d) :
    List (List (Row.WeightedClause n (baseWidth 3 q.p.t) d)) :=
  q.rows.map (HashInputProgram.Expansion.weightedRow q.p.t d q.source)

def sourceJets (q : Factor.Spec r Q n d) (s : Fin 768 → List Bool) :
    ℕ → Fin n → Squarefree.Jet (Fin n) (q.p.model.O q.p.t) :=
  fun id v => Factor.factorJet q.p q.ps q.packing n id v.val q.theta s

/-- Dispatch agrees also on the marked ID and on every neutral ID.  Raw
tuple multiplicity is preserved in weightedHashes. -/
theorem value_eq_selectedValue (q : Factor.Spec r Q n d)
    (s : Fin 768 → List Bool) (id : ℕ) :
    q.value s id = AssignmentSemantics.selectedValue q.ctx
      (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
      q.code (sourceJets q s) (weightedHashes q) q.marked q.markedClause id := by
  unfold Factor.Spec.value AssignmentSemantics.selectedValue weightedHashes
  simp only [List.length_map]
  by_cases h : id < q.rows.length
  · simp only [dite_eq_left h, List.getElem_map]
    rfl
  · simp only [dite_eq_right h]
    split <;> rfl

theorem value_function (q : Factor.Spec r Q n d) (s : Fin 768 → List Bool) :
    q.value s = AssignmentSemantics.selectedValue q.ctx
      (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
      q.code (sourceJets q s) (weightedHashes q) q.marked q.markedClause := by
  funext id
  exact value_eq_selectedValue q s id

def assignmentJets (q : Factor.Spec r Q n d) (high bits : List Bool)
    (c : AssignmentContext) (x : List Bool) :=
  sourceJets q (FactorLoop.assignmentReference high bits c x)

def localProduct (q : Factor.Spec r Q n d) (high bits : List Bool)
    (headIds : List Bool → List ℕ) (c : AssignmentContext) (x : List Bool) :
    Squarefree.Jet (Fin n) (q.p.model.O q.p.t) :=
  ((headIds c.head).map (AssignmentSemantics.selectedValue q.ctx
    (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
    q.code (assignmentJets q high bits c x) (weightedHashes q)
    q.marked q.markedClause)).prod

def relation (q : Factor.Spec r Q n d) (high bits : List Bool)
    (headIds : List Bool → List ℕ)
    (zero one : RingProgram.Code (Word (baseWidth 3 q.p.t)) d) :=
  FactorLoop.assignmentRelation
    (fun c x => q.step (FactorLoop.assignmentReference high bits c x))
    (fun c _ => headIds c.head) q.one
    (fun c x => AssignmentSemantics.coefficient zero one x c.support c.headMask)

def semantic (q : Factor.Spec r Q n d) (high bits : List Bool)
    (headIds : List Bool → List ℕ) (c : AssignmentContext) (x : List Bool) :
    Squarefree.Jet (Fin n) (q.p.model.O q.p.t) :=
  Moments.ringScalar (if LeafWeightProgram.good x c.support c.headMask
    then (1 : q.p.model.O q.p.t) else 0) *
      Squarefree.canonical q.u q.J (localProduct q high bits headIds c x)

/-- The physical fold supplies only a relation on its actual raw result.
No equality between raw results of different executions is needed. -/
theorem contribution_denote (q : Factor.Spec r Q n d) (high bits : List Bool)
    (headIds : List Bool → List ℕ)
    (zero one : RingProgram.Code (Word (baseWidth 3 q.p.t)) d)
    (hzero : q.p.ops.decode zero=0) (hone : q.p.ops.decode one=1)
    (c : AssignmentContext) (x : List Bool)
    (value : Contribution n (baseWidth 3 q.p.t) d)
    (hr : relation q high bits headIds zero one c x value) :
    contributionDenote 3 q.p.t q.p.modulus q.p.cache
      (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t)) value =
        semantic q high bits headIds c x := by
  have h := FactorLoop.relation_contribution_denote q.p.modulus q.p.cache
    (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t))
    q.u q.J zero one hzero hone q.one q.oneValue
    (fun c x => q.step (FactorLoop.assignmentReference high bits c x))
    (fun c _ => headIds c.head)
    (fun c x => q.value (FactorLoop.assignmentReference high bits c x))
    (fun _ _ _ _ _ h => h) c x value hr
  simpa only [semantic, localProduct, assignmentJets, value_function] using h

/-- The weight reads the current head assignment, whereas the source jets
read the independently merged baseline stored in assignmentReference. -/
theorem semantic_typed (q : Factor.Spec r Q n d) (high bits : List Bool)
    (headIds : List Bool → List ℕ) {G : Type*} [Fintype G] [DecidableEq G]
    (assignment : Fin n → Bool) (support : Squarefree.Support (Fin n))
    (head : Fin n → G) (g : G) (c : AssignmentContext)
    (hs : c.support=LeafWeightProgram.supportBits support)
    (hh : c.headMask=LeafWeightProgram.headBits head g) :
    semantic q high bits headIds c (List.ofFn assignment) =
      Moments.ringScalar (Moments.localBoolWeight head support g
        (fun i => assignment i.val)) *
      Squarefree.canonical q.u q.J
        (localProduct q high bits headIds c (List.ofFn assignment)) := by
  unfold semantic
  rw [hs,hh,LeafWeightProgram.localBoolWeight_eq]

theorem contribution_denote_typed (q : Factor.Spec r Q n d) (high bits : List Bool)
    (headIds : List Bool → List ℕ)
    (zero one : RingProgram.Code (Word (baseWidth 3 q.p.t)) d)
    (hzero : q.p.ops.decode zero=0) (hone : q.p.ops.decode one=1)
    {G : Type*} [Fintype G] [DecidableEq G]
    (assignment : Fin n → Bool) (support : Squarefree.Support (Fin n))
    (head : Fin n → G) (g : G) (c : AssignmentContext)
    (hs : c.support=LeafWeightProgram.supportBits support)
    (hh : c.headMask=LeafWeightProgram.headBits head g)
    (value : Contribution n (baseWidth 3 q.p.t) d)
    (hr : relation q high bits headIds zero one c (List.ofFn assignment) value) :
    contributionDenote 3 q.p.t q.p.modulus q.p.cache
      (LiftRing.of (q.p.model.F q.p.t)) (RingBasis.basis (q.p.model.F q.p.t)) value =
      Moments.ringScalar (Moments.localBoolWeight head support g
        (fun i => assignment i.val)) *
      Squarefree.canonical q.u q.J
        (localProduct q high bits headIds c (List.ofFn assignment)) :=
  (contribution_denote q high bits headIds zero one hzero hone c _ value hr).trans
    (semantic_typed q high bits headIds assignment support head g c hs hh)

end SubexponentialSAT.SqrtLog.LeafProgram.AssignmentConcrete

end

end OAI.Algorithms
