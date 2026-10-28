import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluation
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSignatureLocality
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEvaluation
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteBaseline
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteResidualProduct
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentConcreteEmbedding
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSignatureBound

/-! Concrete source locality for the streamed head evaluation.
The source correspondence is `NodeConcrete.fixedSourceRow_baseline_eq` in
LeafProgramNodeConcretePlan, the actual residualJet in
LeafProgramNodeConcreteResidual, and residualProduct in
LeafProgramNodeConcreteResidualProduct. Fixed-high bits cancel in the full
integer signatures; every correction specialization uses one common U. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog



open OAI SubexpLiftRing SubexpQuarticRing
open MulticolorTypes Subexp.ConstructivePacking
open LeafProgram LeafProgram.NodeConcrete
open LayoutProgram PerturbationAssembly Polynomial

noncomputable section

variable {r Q d n : ℕ}

/-- The actually stored baseline is equal under the owned-head bits and all
foreign full keys. Fixed-high coordinates cancel in the integer signatures. -/
theorem baseline_locality (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (howner : ∀ i,(ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r) (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (H : Finset (Fin n)) (node : Fin Q) (g : Fin r)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (htheta : p.ops.decode theta=p.model.node p.t Q p.ht p.hfield node)
    (a b : Fin 768 → List Bool)
    (hhigh : ∀ v ∈ H,(a 145).getD v.val false=(b 145).getD v.val false)
    (hown : ∀ v : ResidualEmbedding.Free H,head node v.val=g →
      (a 145).getD v.val.val false=(b 145).getD v.val.val false)
    (hother : ∀ h,h≠g → freeLabel p ps P owner head H node h
        (fun v => (a 145).getD v.val.val.val false) =
      freeLabel p ps P owner head H node h (fun v => (b 145).getD v.val.val.val false))
    (f j : ℕ) (hj : (j,n+f)∈ps)
    (hslot : (P.label (planIndex ps n f j hj)).slot 0 node=g) :
    baseline (n:=n) p ps P theta a f j=baseline (n:=n) p ps P theta b f j := by
  have he := fixedSourceRow_baseline_eq p ps P owner howner head hhead f j hj node
    (fun v => boolInt ((a 145).getD v.val false))
    (fun v => boolInt ((b 145).getD v.val false))
    (by
      intro v hv
      apply congrArg boolInt
      by_cases hh : v∈H
      · exact hhigh v hh
      · exact hown ⟨v,hh⟩ (hv.trans hslot))
    (by
      intro h hh
      have hf := signature_eq_of_free H (head node) h
        (fun k v => LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node k.val v.val)
        (fun v => (a 145).getD v.val false) (fun v => (b 145).getD v.val false)
        hhigh (hother h (by simpa only [hslot] using hh))
      exact hf)
  simpa only [baseline,boolInt_cast,←htheta,HashInput.boolValue] using he

/-- This is equality of the actual source jets before correction evaluation.
The missing-incidence branch is zero and the high branch is the common fixed bit. -/
theorem residualJet_locality (p : SourceBank.Parameters r Q d) (ps : List (ℕ × ℕ))
    (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (howner : ∀ i,(ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r) (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (H : Finset (Fin n)) (high : H → Bool) (node : Fin Q) (g : Fin r)
    (theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d)
    (htheta : p.ops.decode theta=p.model.node p.t Q p.ht p.hfield node)
    (a b : Fin 768 → List Bool)
    (hhigh : ∀ v ∈ H,(a 145).getD v.val false=(b 145).getD v.val false)
    (hown : ∀ v : ResidualEmbedding.Free H,head node v.val=g →
      (a 145).getD v.val.val false=(b 145).getD v.val.val false)
    (hother : ∀ h,h≠g → freeLabel p ps P owner head H node h
        (fun v => (a 145).getD v.val.val.val false) =
      freeLabel p ps P owner head H node h (fun v => (b 145).getD v.val.val.val false))
    (f : ℕ) (hslot : ∀ j (hj : (j,n+f)∈ps),
      (P.label (planIndex ps n f j hj)).slot 0 node=g) :
    residualJet p ps P H high theta a f=residualJet p ps P H high theta b f := by
  funext j
  unfold residualJet
  by_cases hh : j∈H
  · simp only [dite_eq_left hh]
  · simp only [dite_eq_right hh]
    apply congrArg (Moments.incidenceJet _ (p.ops.decode theta))
    by_cases hj : (j.val,n+f)∈ps
    · exact baseline_locality p ps P owner howner head hhead H node g theta htheta
        a b hhigh hown hother f j.val hj (hslot j.val hj)
    · simp [baseline,fixedSourceRow,LayoutSourceRowsProgram.sourceRowFamily,hj]


/-- The actual selected-factor product for one owned color group. IDs outside
the hash and optional marked range retain the original neutral-factor branch. -/
def sourceProduct (q : Factor.Spec r Q n d) (H : Finset (Fin n)) (high : H → Bool)
    (state : Fin 768 → List Bool) (ids : List ℕ) :=
  Squarefree.canonical q.u q.J ((ids.map
    (AssignmentConcrete.residualValue q.ctx (q.p.model.base q.p.t)
      (RingBasis.basis (q.p.model.F q.p.t)) q.code
      (residualJet q.p q.ps q.packing H high q.theta state)
      (AssignmentConcrete.weightedHashes q) q.marked q.markedClause)).prod)

/-- The actual retained source product has Boolean degree at most its Taylor
index, including the neutral-factor and empty-group cases. -/
theorem sourceProduct_admissible (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool)
    (state : Fin 768 → List Bool) (ids : List ℕ) :
    Squarefree.Admissible (sourceProduct q H high state ids) :=
  AssignmentConcrete.residual_product_admissible q.ctx (q.p.model.base q.p.t)
    (RingBasis.basis (q.p.model.F q.p.t)) q.code
    (residualJet q.p q.ps q.packing H high q.theta state)
    (residualJet_admissible q H high state) (AssignmentConcrete.weightedHashes q)
    q.marked q.markedClause ids

/-- Every coefficient supplied to finite differences satisfies its precise
Taylor-degree bound; no restriction on J relative to the ambient size is used. -/
theorem sourceProduct_coefficient_bounded (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool)
    (state : Fin 768 → List Bool) (ids : List ℕ) (u z : ℕ) :
    Squarefree.Bounded z (((sourceProduct q H high state ids).coeff u).coeff z) :=
  sourceProduct_admissible q H high state ids u z

/-- Admissibility of the actual product over all colored factor groups,
required by the grouped finite-difference query. -/
theorem colored_source_admissible (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool)
    (state : Fin 768 → List Bool) (ids : List ℕ) (color : ℕ → Fin r) :
    Squarefree.Admissible
      (∏ g : Fin r, sourceProduct q H high state (ids.filter (fun f => color f = g))) := by
  apply Squarefree.admissible_prod
  intro g _
  exact sourceProduct_admissible q H high state _

/-- Source factor semantics read only the actual ambient assignment word;
all caches and physical scratch stacks are irrelevant to the polynomial. -/
theorem sourceProduct_assignment_word (q : Factor.Spec r Q n d)
    (H : Finset (Fin n)) (high : H → Bool)
    (a b : Fin 768 → List Bool) (h145 : a 145=b 145) (ids : List ℕ) :
    sourceProduct q H high a ids=sourceProduct q H high b ids := by
  have he : residualJet q.p q.ps q.packing H high q.theta a =
      residualJet q.p q.ps q.packing H high q.theta b := by
    funext f j
    unfold residualJet
    split
    · rfl
    · apply congrArg (Moments.incidenceJet _ (q.p.ops.decode q.theta))
      simp only [baseline,h145]
  unfold sourceProduct
  rw [he]

/-- Whole selected group products agree as squarefree jets, before applying
the one shared correction U. All actual incidence rows use original IDs. -/
theorem sourceProduct_locality (q : Factor.Spec r Q n d)
    (owner : Fin q.ps.length → Fin n) (howner : ∀ i,(q.ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(q.packing.label i).head t=head t (owner i))
    (H : Finset (Fin n)) (high : H → Bool) (node : Fin Q) (g : Fin r)
    (htheta : q.p.ops.decode q.theta=q.p.model.node q.p.t Q q.p.ht q.p.hfield node)
    (a b : Fin 768 → List Bool)
    (hhigh : ∀ v ∈ H,(a 145).getD v.val false=(b 145).getD v.val false)
    (hown : ∀ v : ResidualEmbedding.Free H,head node v.val=g →
      (a 145).getD v.val.val false=(b 145).getD v.val.val false)
    (hother : ∀ h,h≠g → freeLabel q.p q.ps q.packing owner head H node h
        (fun v => (a 145).getD v.val.val.val false) =
      freeLabel q.p q.ps q.packing owner head H node h
        (fun v => (b 145).getD v.val.val.val false))
    (ids : List ℕ) (hslot : ∀ f ∈ ids, ∀ j (hj : (j,n+f)∈q.ps),
      (q.packing.label (planIndex q.ps n f j hj)).slot 0 node=g) :
    sourceProduct q H high a ids=sourceProduct q H high b ids := by
  unfold sourceProduct
  apply congrArg (Squarefree.canonical q.u q.J)
  apply congrArg List.prod
  apply List.map_congr_left
  intro f hf
  have he := residualJet_locality q.p q.ps q.packing owner howner head hhead H high node g
    q.theta htheta a b hhigh hown hother f (hslot f hf)
  unfold AssignmentConcrete.residualValue
  rw [he]

/-- Immediate specialization uses the identical U for both original
assignments; equality therefore survives the actual dense projection. -/
theorem sourceProduct_specialize_locality (q : Factor.Spec r Q n d)
    (owner : Fin q.ps.length → Fin n) (howner : ∀ i,(q.ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(q.packing.label i).head t=head t (owner i))
    (H : Finset (Fin n)) (high : H → Bool) (node : Fin Q) (g : Fin r)
    (htheta : q.p.ops.decode q.theta=q.p.model.node q.p.t Q q.p.ht q.p.hfield node)
    (a b : Fin 768 → List Bool)
    (hhigh : ∀ v ∈ H,(a 145).getD v.val false=(b 145).getD v.val false)
    (hown : ∀ v : ResidualEmbedding.Free H,head node v.val=g →
      (a 145).getD v.val.val false=(b 145).getD v.val.val false)
    (hother : ∀ h,h≠g → freeLabel q.p q.ps q.packing owner head H node h
        (fun v => (a 145).getD v.val.val.val false) =
      freeLabel q.p q.ps q.packing owner head H node h
        (fun v => (b 145).getD v.val.val.val false))
    (ids : List ℕ) (hslot : ∀ f ∈ ids, ∀ j (hj : (j,n+f)∈q.ps),
      (q.packing.label (planIndex q.ps n f j hj)).slot 0 node=g)
    (U : ResidualEmbedding.Free H → Bool) :
    QueryEvaluation.specializeDense q.u q.J U (sourceProduct q H high a ids) =
      QueryEvaluation.specializeDense q.u q.J U (sourceProduct q H high b ids) :=
  congrArg (QueryEvaluation.specializeDense q.u q.J U)
    (sourceProduct_locality q owner howner head hhead H high node g htheta
      a b hhigh hown hother ids hslot)

/-- Canonical semantic state for the complete ambient assignment. Native
state comparisons need only identify its actual assignment word at145. -/
def stateFor (H : Finset (Fin n)) (high : H → Bool)
    (x : ResidualEmbedding.Free H → Bool) : Fin 768 → List Bool :=
  fun i => if i=145 then List.ofFn (HighIncidence.glue H high x) else []

@[simp] theorem stateFor_get (H : Finset (Fin n)) (high : H → Bool)
    (x : ResidualEmbedding.Free H → Bool) (v : Fin n) :
    (stateFor H high x 145).getD v.val false=HighIncidence.glue H high x v := by
  simp [stateFor, List.getD_eq_getElem?_getD, v.isLt]

/-- Concrete hlocal for the actual colored selected-factor lists. Own-head
agreement and foreign full integer keys suffice; no evaluator, layout service,
or correction-dependent representative is assumed. -/
theorem colored_source_hlocal (q : Factor.Spec r Q n d)
    (owner : Fin q.ps.length → Fin n) (howner : ∀ i,(q.ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(q.packing.label i).head t=head t (owner i))
    (H : Finset (Fin n)) (high : H → Bool) (node : Fin Q)
    (htheta : q.p.ops.decode q.theta=q.p.model.node q.p.t Q q.p.ht q.p.hfield node)
    (ids : List ℕ) (color : ℕ → Fin r)
    (hslot : ∀ f ∈ ids, ∀ j (hj : (j,n+f)∈q.ps),
      (q.packing.label (planIndex q.ps n f j hj)).slot 0 node=color f)
    (U : ResidualEmbedding.Free H → Bool) (g : Fin r)
    (x y : ResidualEmbedding.Free H → Bool)
    (hown : Moments.split (fun v : ResidualEmbedding.Free H => head node v.val) x g =
      Moments.split (fun v : ResidualEmbedding.Free H => head node v.val) y g)
    (hother : ∀ h,h≠g → freeLabel q.p q.ps q.packing owner head H node h
        (Moments.split (fun v : ResidualEmbedding.Free H => head node v.val) x h) =
      freeLabel q.p q.ps q.packing owner head H node h
        (Moments.split (fun v : ResidualEmbedding.Free H => head node v.val) y h)) :
    QueryEvaluation.specializeDense q.u q.J U
        (sourceProduct q H high (stateFor H high x) (ids.filter (fun f => color f=g))) =
      QueryEvaluation.specializeDense q.u q.J U
        (sourceProduct q H high (stateFor H high y) (ids.filter (fun f => color f=g))) := by
  apply sourceProduct_specialize_locality q owner howner head hhead H high node g htheta
  · intro v hv
    simp only [stateFor_get, HighIncidence.glue, dite_eq_left hv]
  · intro v hv
    simpa only [stateFor_get, HighIncidence.glue, dite_eq_right v.property, Moments.split]
      using congrFun hown ⟨v,hv⟩
  · intro h hh
    have hx : (fun v : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) h =>
        (stateFor H high x 145).getD v.val.val.val false) =
        Moments.split (fun v : ResidualEmbedding.Free H => head node v.val) x h := by
      funext v
      simp only [stateFor_get, HighIncidence.glue, dite_eq_right v.val.property,
        Moments.split]
    have hy : (fun v : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) h =>
        (stateFor H high y 145).getD v.val.val.val false) =
        Moments.split (fun v : ResidualEmbedding.Free H => head node v.val) y h := by
      funext v
      simp only [stateFor_get, HighIncidence.glue, dite_eq_right v.val.property,
        Moments.split]
    rw [hx,hy]
    exact hother h hh
  · intro f hf j hj
    have hh : f∈ids ∧ color f=g := by simpa only [List.mem_filter,decide_eq_true_eq] using hf
    exact (hslot f hh.1 j hj).trans hh.2

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSourceLocality
