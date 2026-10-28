import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TupleRunBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryHeadSourceFacts
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEnvelopeBudgets
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryModelBudgets

/-! The measured callback pays native mask setup, the complete attained-tuple
run (including ascent), and the signed commit. Its finite-difference iterator
is compared to the original explicit resource record with one fixed power. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost

open OAI SqrtLog SubexpLiftRing SubexpQuarticRing
open SignatureTupleSource SignatureTupleTraversal SignatureTupleDFS
open CostAssembly.Polynomial
open scoped BigOperators

/-- A polynomial envelope for the actual signed scaler, dense addition,
two mask scans, environment setup and cleanup. -/
def commitEnvelope (A : ℕ) : ℕ :=
  51000*(QueryHeadBudgets.compact A+1)+20*A+6000000*(6*A+1)^10+
    6*(A*A*(2*(A+A+A)+2*(A*(2*A))+2))+30

def localEnvelope (A : ℕ) : ℕ :=
  QueryPairEvaluation.startBudget A (QueryHeadBudgets.compact A)+commitEnvelope A

def coefficient (A : ℕ) : ℕ := localEnvelope A+TupleRunBudgets.runCoefficient A

theorem commit_le {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (N A : ℕ)
    (hn : n ≤ A) (hN : N ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hJ : q.J ≤ A) :
    QueryPairEvaluation.commitBudget q N (QueryHeadBudgets.compact A) ≤ commitEnvelope A := by
  have hlocal := TruncatedRingProgram.localBudget_le n (baseWidth 3 q.p.t) d q.p.t q.J 0
  have hscale := TruncatedRingProgram.scalingBudget_le_local n (baseWidth 3 q.p.t) d q.p.t q.J 0
  have hadd := TruncatedRingProgram.additionBudget_le_local n (baseWidth 3 q.p.t) d q.p.t q.J 0
  have hb : TruncatedRingProgram.localBudget n (baseWidth 3 q.p.t) d q.p.t q.J 0 ≤
      3000000*(6*A+1)^10 := by
    apply hlocal.trans
    simp only [RingProgram.ternary_baseWidth]
    gcongr
    omega
  have hbytes : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) ≤
      A*A*(2*(A+A+A)+2*(A*(2*A))+2) := by
    simp only [RingProgram.ternary_baseWidth]
    gcongr
  unfold QueryPairEvaluation.commitBudget QueryProgram.pairUpdateBudget
    QueryProgram.signedAccumulateBudget QueryProgram.signedScalingBudget commitEnvelope
  omega

private theorem compact_ordinary : Ordinary QueryHeadBudgets.compact := by
  obtain ⟨C,e,h⟩ := QueryHeadBudgets.caps_polynomial
  exact ⟨C,e,fun A => (h A).1⟩

theorem coefficient_polynomial : ∃ C e : ℕ, ∀ A, coefficient A ≤ C*(A+1)^e := by
  change Ordinary coefficient
  have hstart : Ordinary (fun A => QueryPairEvaluation.startBudget A (QueryHeadBudgets.compact A)) := by
    unfold QueryPairEvaluation.startBudget
    exact ordinary_add (ordinary_add
      (ordinary_mul (ordinary_const 300)
        (ordinary_add (ordinary_add compact_ordinary ordinary_id) (ordinary_const 1)))
      (ordinary_mul (ordinary_const 2) compact_ordinary)) (ordinary_const 5)
  have hbytes : Ordinary (fun A => A*A*(2*(A+A+A)+2*(A*(2*A))+2)) :=
    ordinary_mul (ordinary_mul ordinary_id ordinary_id)
      (ordinary_add (ordinary_add
        (ordinary_mul (ordinary_const 2) (ordinary_add (ordinary_add ordinary_id ordinary_id) ordinary_id))
        (ordinary_mul (ordinary_const 2) (ordinary_mul ordinary_id (ordinary_mul (ordinary_const 2) ordinary_id))))
        (ordinary_const 2))
  have hcommit : Ordinary commitEnvelope := by
    unfold commitEnvelope
    exact ordinary_add (ordinary_add (ordinary_add (ordinary_add
      (ordinary_mul (ordinary_const 51000) (ordinary_add compact_ordinary (ordinary_const 1)))
      (ordinary_mul (ordinary_const 20) ordinary_id))
      (ordinary_mul (ordinary_const 6000000)
        (ordinary_pow (ordinary_add (ordinary_mul (ordinary_const 6) ordinary_id) (ordinary_const 1)) 10)))
      (ordinary_mul (ordinary_const 6) hbytes)) (ordinary_const 30)
  exact ordinary_add (ordinary_add hstart hcommit) TupleRunBudgets.runCoefficient_polynomial

/-- All callback coefficients are instantiated at the same compact cap as
the actual tuple run. No successful callback or evaluator is a hypothesis. -/
theorem callback_le (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (N A height : ℕ)
    (hN : N ≤ s.input.n) (hs : s.bound ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A)
    (hu : q.u ≤ A) (hJ : q.J ≤ A) (hR : q.p.R = s.input.R)
    (hw : q.p.width = s.input.width) (hp : q.p.power = s.input.power) :
    QueryPairEvaluation.callbackBudget s q N (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
      (QueryHeadBudgets.transient A) height ≤
      coefficient A*(s.input.r+1)*SignatureTupleRun.tupleCount s.key s.input.r*4^height := by
  have hn := (NodeTime.inputBounds s.input s.source s.ready s.bound s.bounded).n.trans hs
  have hstart : QueryPairEvaluation.startBudget s.input.n (QueryHeadBudgets.compact A) ≤
      QueryPairEvaluation.startBudget A (QueryHeadBudgets.compact A) := by
    unfold QueryPairEvaluation.startBudget
    omega
  have hcommit := commit_le q N A hn (hN.trans hn) hd ht hJ
  have hrun := (TupleRunBudgets.run_bounds s q A hs hd ht hu hJ hR hw hp).2 height
  have hK : 1 ≤ SignatureTupleRun.tupleCount s.key s.input.r :=
    StreamedQueryCostBudgets.attained_inventory_pos s.key s.input.r
  have hfactor : 1 ≤ (s.input.r+1)*SignatureTupleRun.tupleCount s.key s.input.r*4^height := by
    simpa only [one_mul] using Nat.mul_le_mul
      (Nat.mul_le_mul (show 1 ≤ s.input.r+1 by omega) hK)
      (Nat.one_le_pow height 4 (by decide))
  have hpaid : QueryPairEvaluation.startBudget s.input.n (QueryHeadBudgets.compact A)+
      QueryPairEvaluation.commitBudget q N (QueryHeadBudgets.compact A) ≤
      localEnvelope A*((s.input.r+1)*SignatureTupleRun.tupleCount s.key s.input.r*4^height) := by
    apply (Nat.add_le_add hstart hcommit).trans
    exact (Nat.mul_one (localEnvelope A)).symm.le.trans (Nat.mul_le_mul_left _ hfactor)
  unfold QueryPairEvaluation.callbackBudget coefficient
  calc
    _ ≤ localEnvelope A*((s.input.r+1)*SignatureTupleRun.tupleCount s.key s.input.r*4^height)+
        TupleRunBudgets.runCoefficient A*(s.input.r+1)*SignatureTupleRun.tupleCount s.key s.input.r*4^height := by omega
    _ = _ := by ring

/-- The explicit pair-loop coefficient has a fixed polynomial degree before
the source, the node, the supports or the attained signatures are chosen. -/
def pairCoefficient (A : ℕ) : ℕ := (coefficient A+46)*(A+1)*(3*A+1)

theorem pairCoefficient_polynomial : ∃ C e : ℕ, ∀ A, pairCoefficient A ≤ C*(A+1)^e := by
  change Ordinary pairCoefficient
  exact ordinary_mul
    (ordinary_mul (ordinary_add coefficient_polynomial (ordinary_const 46))
      (ordinary_add ordinary_id (ordinary_const 1)))
    (ordinary_add (ordinary_mul (ordinary_const 3) ordinary_id) (ordinary_const 1))

/-- The actual source-prefix bound contains only local polynomial work and
the retained words. Neither attained counts nor an exponential time occurs. -/
def pairSpaceEnvelope (A : ℕ) : ℕ := coefficient A+896*QueryHeadBudgets.compact A+13

theorem pairSpaceEnvelope_polynomial : ∃ C e : ℕ, ∀ A, pairSpaceEnvelope A ≤ C*(A+1)^e := by
  change Ordinary pairSpaceEnvelope
  exact ordinary_add (ordinary_add coefficient_polynomial
    (ordinary_mul (ordinary_const 896) compact_ordinary)) (ordinary_const 13)

/-- This is precisely the all-prefix stack bound exported by the actual
pair run, with the same compact cap used at every callback boundary. -/
theorem pair_space_le (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (N A : ℕ)
    (hN : N ≤ s.input.n) (hs : s.bound ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A)
    (hu : q.u ≤ A) (hJ : q.J ≤ A) (hR : q.p.R = s.input.R)
    (hw : q.p.width = s.input.width) (hp : q.p.power = s.input.power) :
    max (QueryPairEvaluation.callbackSpace s q N (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.transient A)) (896*QueryHeadBudgets.compact A+13) ≤ pairSpaceEnvelope A := by
  have hn := (NodeTime.inputBounds s.input s.source s.ready s.bound s.bounded).n.trans hs
  have hstart : QueryPairEvaluation.startBudget s.input.n (QueryHeadBudgets.compact A) ≤
      QueryPairEvaluation.startBudget A (QueryHeadBudgets.compact A) := by
    unfold QueryPairEvaluation.startBudget
    omega
  have hcommit := commit_le q N A hn (hN.trans hn) hd ht hJ
  have hcomplete := (TupleRunBudgets.run_bounds s q A hs hd ht hu hJ hR hw hp).1
  unfold QueryPairEvaluation.callbackSpace pairSpaceEnvelope coefficient localEnvelope
  exact max_le (max_le (by omega) (by omega)) (by omega)

private theorem square_inventory (M K H : ℕ) (hK : 1 ≤ K) :
    M^2*K*4^H ≤ (M*K*2^H)^2 := by
  have hk : K ≤ K^2 := by nlinarith
  calc
    _ ≤ M^2*K^2*4^H := by gcongr
    _ = _ := by rw [show (4:ℕ)=2^2 by norm_num,←pow_mul,mul_pow,mul_pow]; ring

/-- Actual start/run/commit and iterator costs are dominated by the square
of the original assembled budget. The remaining premises identify the actual
jet order, selected-rank inventory and balanced head maximum in that record. -/
theorem pair_cost_le_assembled (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (k N n A height : ℕ) (p : CostAssembly.Resources)
    (hN : N ≤ s.input.n) (hsn : s.input.n ≤ n) (hs : s.bound ≤ A)
    (hd : d ≤ A) (ht : q.p.t ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (hR : q.p.R = s.input.R) (hw : q.p.width = s.input.width) (hp : q.p.power = s.input.power)
    (horder : q.J = CostAssembly.jetOrder k n p)
    (hbits : 1 ≤ p.bits) (hheads : 1 ≤ p.heads)
    (hK : SignatureTupleRun.tupleCount s.key s.input.r ≤ p.labelBase^p.labelRows)
    (hheight : height ≤ p.headSize) :
    DifferencePairsProgram.cost
      (QueryPairEvaluation.callbackBudget s q N (QueryHeadBudgets.compact A)
        (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
        (QueryHeadBudgets.transient A) height) N q.J ≤
      pairCoefficient A*CostAssembly.assembledWork k n p^2+10 := by
  let K := SignatureTupleRun.tupleCount s.key s.input.r
  let M := SupportProgram.count n q.J
  have hk : 1 ≤ K := StreamedQueryCostBudgets.attained_inventory_pos s.key s.input.r
  have hi := NodeTime.inputBounds s.input s.source s.ready s.bound s.bounded
  have hna := hN.trans (hi.n.trans hs)
  have hra := hi.r.trans hs
  have hcb := callback_le s q N A height hN hs hd ht hu hJ hR hw hp
  have hfactor : 1 ≤ (s.input.r+1)*K*4^height := by
    simpa only [one_mul] using Nat.mul_le_mul
      (Nat.mul_le_mul (show 1 ≤ s.input.r+1 by omega) hk)
      (Nat.one_le_pow height 4 (by decide))
  have h46 : 46 ≤ 46*((s.input.r+1)*K*4^height) :=
    (Nat.mul_one 46).symm.le.trans (Nat.mul_le_mul_left _ hfactor)
  have hcallback : QueryPairEvaluation.callbackBudget s q N (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
      (QueryHeadBudgets.transient A) height+46 ≤ (coefficient A+46)*(s.input.r+1)*K*4^height := by
    calc
      _ ≤ coefficient A*(s.input.r+1)*K*4^height+46*((s.input.r+1)*K*4^height) := Nat.add_le_add hcb h46
      _ = _ := by ring
  have hcombined : M*K*2^height ≤ CostAssembly.assembledWork k n p := by
    dsimp only [M]
    rw [horder]
    rw [Nat.mul_assoc]
    apply (Nat.mul_le_mul_left _ (StreamedQueryCostBudgets.inventory_head_le_enumeration K height
      p.labelBase p.labelRows p.heads p.headSize hK hheight hheads)).trans
    exact StreamedQueryCostBudgets.support_enumeration_le_sparseWork n _ p.setup
      (CostAssembly.hashCalls n p.clauses (SparseCode.distanceDenom p.clauses p.initialOccurrence))
      (2^p.branchVars) p.labelBase p.labelRows p.heads p.headSize p.bits p.ordinary
      (by unfold CostAssembly.hashCalls; omega) (Nat.one_le_pow _ _ (by decide)) hbits
  have hpair : DifferencePairs.pairCount N q.J ≤ M^2 := pairCount_le_ambient_support_square (hN.trans hsn) q.J
  unfold DifferencePairsProgram.cost
  calc
    _ ≤ ((coefficient A+46)*(s.input.r+1)*K*4^height)*(3*N+1)*M^2+10 := by gcongr
    _ = (coefficient A+46)*(s.input.r+1)*(3*N+1)*(M^2*K*4^height)+10 := by ring
    _ ≤ pairCoefficient A*(M*K*2^height)^2+10 := by
      unfold pairCoefficient
      gcongr
      exact square_inventory M K height hk
    _ ≤ _ := by gcongr

/-- Uniform fixed coefficients turn the actual pair cost into a fixed power
of the original explicit budget plus the physical local input cap. -/
theorem pair_cost_fixed_power : ∃ C e : ℕ, ∀ (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (k N n A height : ℕ) (p : CostAssembly.Resources),
    N ≤ s.input.n → s.input.n ≤ n → s.bound ≤ A → d ≤ A → q.p.t ≤ A → q.u ≤ A → q.J ≤ A →
    q.p.R = s.input.R → q.p.width = s.input.width → q.p.power = s.input.power →
    q.J = CostAssembly.jetOrder k n p → 1 ≤ p.bits → 1 ≤ p.heads →
    SignatureTupleRun.tupleCount s.key s.input.r ≤ p.labelBase^p.labelRows → height ≤ p.headSize →
    DifferencePairsProgram.cost
      (QueryPairEvaluation.callbackBudget s q N (QueryHeadBudgets.compact A)
        (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
        (QueryHeadBudgets.transient A) height) N q.J ≤
      C*(CostAssembly.assembledWork k n p+A+1)^e := by
  obtain ⟨C,e,hpoly⟩ := pairCoefficient_polynomial
  refine ⟨C+10,e+2,?_⟩
  intro s d q k N n A height p hN hsn hs hd ht hu hJ hR hw hp horder hbits hheads hK hheight
  apply (pair_cost_le_assembled s q k N n A height p hN hsn hs hd ht hu hJ hR hw hp
    horder hbits hheads hK hheight).trans
  let X := CostAssembly.assembledWork k n p+A+1
  have hx : 1 ≤ X := by dsimp [X]; omega
  have ha : A+1 ≤ X := by dsimp [X]; omega
  have hwork : CostAssembly.assembledWork k n p ≤ X := by dsimp [X]; omega
  have hone : 1 ≤ X^(e+2) := Nat.one_le_pow _ _ hx
  calc
    _ ≤ C*(A+1)^e*CostAssembly.assembledWork k n p^2+10 := by gcongr; exact hpoly A
    _ ≤ C*X^e*X^2+10 := by gcongr
    _ = C*X^(e+2)+10 := by rw [pow_add]; ring
    _ ≤ (C+10)*X^(e+2) := by nlinarith

section Addressed

open MulticolorTypes LeafHeadSetupProgram LeafParametersProgram

variable (front : LeafQueryFrontend.Query) (k B C degree qi exponent : ℕ)
  (guard : LeafParametersProgram.Guard (front.input k))
  (first : Word (LeafProgram.Query.packingProblem front k guard).r
    (LeafProgram.Query.packingProblem front k guard).Q)
  (tail : List (Word (LeafProgram.Query.packingProblem front k guard).r
    (LeafProgram.Query.packingProblem front k guard).Q))
  (node : Fin (LeafProgram.Query.packingProblem front k guard).Q)
  (physical : LeafHeadSetupProgram.Data)
  (ready : Native.Ready (Native.queryInputsAddressed front k guard first tail node) physical)
  (bound : ℕ) (bounded : SubexpSetupStorage.WordBound bound physical)
  (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
  (hc : CacheCorrect (Native.queryInputsAddressed front k guard first tail node).height
    (unary (Native.queryInputsAddressed front k guard first tail node).R)
    (Native.queryInputsAddressed front k guard first tail node).width words)

local notation "src" => QueryHeadSourceFacts.addressedSource front k guard first tail node
  physical ready bound bounded ra rd rc words hc
local notation "resources" => ProducedQueryResources.ofPacking front k B C degree qi exponent guard first tail

/-- The actual addressed loader's tuple count uses exactly the original
selected matrices. No key-kernel, rank or successful-layout premise remains. -/
theorem addressed_inventory :
    SignatureTupleRun.tupleCount (src).key (src).input.r ≤
      (resources).labelBase^(resources).labelRows := by
  have hk := StreamedQueryCostBudgets.query_key_inventory_le_ofPacking
    front k B C degree qi exponent guard first tail node (src).key (by
      intro g x y
      change AttainedSignatures.integerKey (fun j i => LayoutProducedMatrix.literalNat
        (ProducedQueryRank.packing (LeafProgram.Query.packingProblem front k guard) first tail)
        (ProducedQueryRank.owner (LeafProgram.Query.packingProblem front k guard))
        (unary (Subexp.TailInterval.intervalStart
          (LeafParametersProgram.produce (front.input k)).r
          (LeafParametersProgram.produce (front.input k)).Q
          (LeafParametersProgram.produce (front.input k)).R)).length
        (LeafParametersProgram.produce (front.input k)).R node j.val
        ((selectedHeads (src).input.n (src).input.rows (src).input.low
          (node.val*(src).input.r+g.val)).get i)) x =
        AttainedSignatures.integerKey (fun j i => LayoutProducedMatrix.literalNat
        (ProducedQueryRank.packing (LeafProgram.Query.packingProblem front k guard) first tail)
        (ProducedQueryRank.owner (LeafProgram.Query.packingProblem front k guard))
        (unary (Subexp.TailInterval.intervalStart
          (LeafParametersProgram.produce (front.input k)).r
          (LeafParametersProgram.produce (front.input k)).Q
          (LeafParametersProgram.produce (front.input k)).R)).length
        (LeafParametersProgram.produce (front.input k)).R node j.val
        ((selectedHeads (src).input.n (src).input.rows (src).input.low
          (node.val*(src).input.r+g.val)).get i)) y ↔ _
      simp only [unary,List.length_replicate]
      rfl)
  unfold SignatureTupleRun.tupleCount
  rw [show (src).input.r = (LeafProgram.Query.packingProblem front k guard).r by rfl]
  exact hk

/-- The exponent is the maximum selected free-head size in the same original
record. Ambient size is used only in its signature-range base. -/
theorem addressed_headSize (depth : ℕ) (hdepth : depth < (src).input.r) :
    (src).headSize depth ≤ (resources).headSize :=
  ProducedQueryResources.selected_length_le front k B C degree qi exponent guard first tail node
    ⟨depth,hdepth⟩

variable (model : Circuit.Model) (padding : Fin 8 → ℕ)
  (model_eq : model = LeafParametersProgram.Execute.guardedModel (front.input k) padding)
variable (positiveT : 0 < (model).val 33) (positiveD : 0 < (model).val 34)
  (modulus : SubexpPreparedQuartic.Modulus 3 ((model).val 33))
  (cache : RingProgram.ScalarCache 3 ((model).val 33))
  (half : RingProgram.ScalarCode 3 ((model).val 33)) (output : LeafRingSetupProgram.Data)
  (produced : LeafRingSetupProgram.Produced model positiveD modulus cache half output)
  (fieldSize : (Native.queryInputsAddressed front k guard first tail node).Q < 3^((model).val 34))
  (valid : front.Valid)
  (positiveJ : 0 < (model).val 42)
  (clauses : List (List (SAT.Literal
    (Fin (Native.queryInputsAddressed front k guard first tail node).n))))
  (encoded : front.clauses = HashInputProgram.Expansion.encodedClauses clauses)

local notation "spec" => QueryReadyConstruction.sourceSpec src model positiveT positiveD
  modulus cache half output produced fieldSize front valid positiveJ clauses encoded

include model_eq valid in
/-- The real guarded parameter bank and authentic factor factory identify
the order in the pair iterator with the order of this original resource record. -/
theorem addressed_order :
    model.val 42 = CostAssembly.jetOrder k (ProducedQueryResources.ambient front) resources := by
  have hm : (front.input k).clauses ≠ 0 := Nat.ne_of_gt guard.2.2.1
  have hQ : (LeafParametersProgram.produce (front.input k)).Q ≠ 0 := by
    have := guard.2.2.2.2.2.2.1
    omega
  exact (congrArg (fun m : Circuit.Model => m.val 42) model_eq).trans
    (((LeafParametersProgram.Execute.guardedModel_public (front.input k) padding 11).trans
    (LeafParametersProgram.Layout.model_jet (front.input k) padding hm hQ)).trans
    (QueryEnvelopeBudgets.produced_order_eq front k B C degree qi exponent guard first tail valid))

include model_eq ready bounded hc positiveT positiveD produced fieldSize valid positiveJ encoded in
/-- The complete measured pair cost for the actual addressed source and
actual produced ring. Every local dimension is read from its bounded scalar
bank, and both exponential factors use the same selected-rank/head record. -/
theorem addressed_pair_cost (A : ℕ) (hbound : bound ≤ A)
    (hbank : ∀ j, (model).val j ≤ A) :
    DifferencePairsProgram.cost
      (QueryPairEvaluation.callbackBudget src spec
        ((src).input.n-(HighMarkedFrontend.highSet front).card)
        (QueryHeadBudgets.compact A) (QueryHeadBudgets.source A)
        (QueryHeadBudgets.arithmetic A) (QueryHeadBudgets.transient A) (resources).headSize)
      ((src).input.n-(HighMarkedFrontend.highSet front).card) (spec).J ≤
      pairCoefficient A*CostAssembly.assembledWork k (ProducedQueryResources.ambient front) resources^2+10 := by
  exact pair_cost_le_assembled src spec k
    ((src).input.n-(HighMarkedFrontend.highSet front).card) (ProducedQueryResources.ambient front)
    A (resources).headSize resources (Nat.sub_le ..) le_rfl hbound
    (hbank 34) (hbank 33) (hbank 33) (hbank 42) rfl rfl rfl
    (addressed_order front k B C degree qi exponent guard first tail model padding model_eq valid)
    (ProducedQueryResources.make_bits_pos ..) (ProducedQueryResources.make_heads_pos ..)
    (addressed_inventory front k B C degree qi exponent guard first tail node physical ready bound bounded
      ra rd rc words hc) le_rfl

include ready bounded hc positiveT positiveD produced fieldSize valid positiveJ encoded in
/-- The same actual addressed source and produced ring have polynomial
all-prefix pair space; the exponential traversal time is never used here. -/
theorem addressed_pair_space (A : ℕ) (hbound : bound ≤ A)
    (hbank : ∀ j, model.val j ≤ A) :
    max (QueryPairEvaluation.callbackSpace src spec
      ((src).input.n-(HighMarkedFrontend.highSet front).card)
      (QueryHeadBudgets.compact A) (QueryHeadBudgets.transient A))
      (896*QueryHeadBudgets.compact A+13) ≤ pairSpaceEnvelope A :=
  pair_space_le src spec _ A (Nat.sub_le ..) hbound
    (hbank 34) (hbank 33) (hbank 33) (hbank 42) rfl rfl rfl

end Addressed

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost
