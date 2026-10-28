import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumNative
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedFrames
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoadBounds

/-! The concrete one-head visitor composes its actual loader, paid key setup,
restricted head rescan and tuple multiplication. Exponential work is kept
separate from the reusable boundary and all-prefix storage bounds. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
open OAI BitProgram StructuredCalls SqrtLog SqrtLog.LeafProgram SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadIdentifierProgram
open BucketTupleProgram.Concrete QueryTupleState SubexpSetupStorage
open scoped BigOperators
noncomputable section

/-- The exact restricted full-signature fiber contributed by one head. -/
def fiberValue {r Q n d : ℕ} (q : Factor.Spec r Q n d) (u : ℕ)
    (node : Fin Q) (H E U : Finset (Fin n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (g : Fin r)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) k → Bool)
    (ids : List ℕ) : Dense (q.p.model.O q.p.t) u q.J :=
  ∑ x : Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) g → Bool,
    if HeadSourceLocality.freeLabel q.p q.ps q.packing owner head H node g x =
        HeadSourceLocality.freeLabel q.p q.ps q.packing owner head H node g (reps g) ∧
        (∀ v, v.val.val ∈ E → x v = true) then
      QueryEvaluation.specializeDense u q.J
        (fun v : ResidualEmbedding.Free H => decide (v.val ∈ U))
        (HeadSourceLocality.sourceProduct q H high
          (HeadSourceLocality.stateFor H high
            (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val)
              (Function.update reps g x))) ids) else 0

/-- The produced ring precision is the retained marker cutoff. -/
def headValue {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (node : Fin Q) (H E U : Finset (Fin n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (g : Fin r)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) k → Bool)
    (ids : List ℕ) : Dense (q.p.model.O q.p.t) q.p.t q.J :=
  fiberValue q q.p.t node H E U high owner head g reps ids

/-- Actual multiplication time after one normalized head sum. -/
def multiplyBudget {r Q n d : ℕ} (q : Factor.Spec r Q n d) (P : ℕ) : ℕ :=
  51000*(P+1)+FactorProductSpace.budget n (baseWidth 3 q.p.t) d q.p.t q.J

def sumBudget {r Q n d : ℕ} (q : Factor.Spec r Q n d) (P S Z B h : ℕ) : ℕ :=
  (2*(HeadEvaluationProgram.StagedGate.bodyPolynomial P+
    HeadAcceptedCorrect.budget q P S Z)+126*B+54*h+286)*2^h

private theorem call_prefix {l steps bound : ℕ} (routine : Program 40 896 l)
    {a b : State 40 896}
    (ht : Trace routine steps (a.withPC (some routine.entry)) (b.withPC none))
    (hs : ∀ elapsed cfg,elapsed ≤ steps →
      Trace routine elapsed (a.withPC (some routine.entry)) cfg →
      ∀ i,(cfg.stacks i).length ≤ bound) :
    QueryExecution.PrefixBound (.call routine) steps a bound := by
  constructor
  exact StructuredSpace.call_stack_bound routine _
    (siteAddress (.call routine)) (exitAddress (.call routine))
    (compiled_site (.call routine) 838 838) ht hs

private theorem word_le_dataBits {r s l : ℕ} (cfg : Cfg r s l) (i : Fin s) :
    (cfg.stacks i).length ≤ dataBits cfg :=
  Finset.single_le_sum (fun j _ => Nat.zero_le ((cfg.stacks j).length)) (Finset.mem_univ i)

/-- Controller words and the full representative baseline survive one head. -/
def retainedPorts : List (Fin 896) :=
  [836,837,838,839,840,842,843,844,845,846,847,851,864,865,866,867,868,869]

private theorem retained_head (i : Fin 896) (hi : i∈retainedPorts) :
    i∈HeadSumNative.retainedPorts := by
  simp only [retainedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

private theorem retained_multiply (i : Fin 896) (hi : i∈retainedPorts) :
    i∉QueryAssembler.pairScratch ∧ i≠61 ∧ i≠70 ∧ i≠852 ∧ i≠853 := by
  simp only [retainedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

/-- This is the fixed head rescan followed by the actual native dense
multiplication. Its semantic hypotheses are source-word identities and
numerical bounds, never an evaluator or successful-layout service. -/
theorem head_multiply_run {r Q n d M P S Z : ℕ} (q : Factor.Spec r Q n d)
    (node : Fin Q) (H E U : Finset (Fin n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (g : Fin r) (pick : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds pick n ↔ ∃ _ : v ∉ H, head node v = g)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) k → Bool)
    (W : List Bool) (c : Fin q.ps.length → Fin (count pick n) → List Bool)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) +
        LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R node j.val
          ((chosenIds pick n).get i))
    (ids : List ℕ) (a : HeadSumProgram.Data)
    (hq : QueryReady q node H high E U M a) (ha : ∀ j, (a.stacks j).length  ≤  P)
    (hshape : a.stacks 651 = List.replicate (count pick n) false)
    (hmask : a.stacks 670 = List.ofFn (fun v : Fin n => pick v.val))
    (hbase : a.stacks 869 = List.ofFn (HighIncidence.glue H high
      (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val) reps)))
    (hW : a.stacks 864 = W)
    (hmatrix : a.stacks 865 = OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words
      ((List.ofFn (fun j => List.ofFn (c j))).map OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words))
    (hkey : a.stacks 866 = BucketProgram.signatureValue W
      (List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
        (chosenIds_bound pick n) (chosenIds_nodup pick n) hs (reps g)))
      (List.ofFn (fun j => List.ofFn (c j))))
    (hE : a.stacks 867 = HighIncidenceProgram.Restriction.selected true
      (List.ofFn (fun v : Fin n => pick v.val)) (LeafWeightProgram.supportBits ⟨E⟩))
    (hH : a.stacks 868 = List.replicate (count pick n) true)
    (hids : a.stacks 175 = ProgramEncoding.encodeRecords (FactorAssignmentLoop.records ids))
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
    (hcount : count pick n+1  ≤  P) (hrows : q.ps.length  ≤  P)
    (hcoeff : ∀ j i, (c j i).length  ≤  P)
    (hcache : 4*M+6  ≤  P)
    (hcapacity : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J  ≤  P)
    (hsize : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
      (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1  ≤  S)
    (hradius : q.p.R+1  ≤  Q) (width : ℕ)
    (hwidth : ∀ f (hf : f < q.rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length  ≤  width)
    (hZ : 1  ≤  Z) (hP : P  ≤  Z) (hbit : q.bitWidth  ≤  Z)
    (hdegree : d * baseWidth 3 q.p.t  ≤  Z)
    (hhashScale : ∀ f (hf : f < q.rows.length),
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length  ≤  Z)
    (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0  ≤  Z)
    (B : ℕ)
    (hlocal : 896*P + HeadEvaluationProgram.StagedGate.bodyPolynomial P +
      HeadAcceptedCorrect.budget q P S Z  ≤  B)
    (hcounter : 9*(count pick n+1)+8  ≤  B)
    {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hpair : PairAccumulatorMeaning q pairValue a)
    (htuple : DenseWord q 852 tupleValue a)
    (hmul : FactorProductSpace.byteBound n (baseWidth 3 q.p.t) d q.p.t q.J ≤ P) :
    ∃ steps b,
      Eval (.seq (HeadSumAssembly.head HeadSumAssembly.accepted)
        QueryAssembler.TupleMultiply.command) steps a b ∧
      QueryReady q node H high E U M b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 (tupleValue*headValue q node H E U high owner head g reps ids) b ∧
      b.stacks 853=[] ∧ QueryMasterFrame a b ∧ WordBound P b ∧
      (∀ i∈retainedPorts,b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      steps ≤ sumBudget q P S Z B (count pick n)+multiplyBudget q P ∧
      QueryExecution.PrefixBound (.seq (HeadSumAssembly.head HeadSumAssembly.accepted)
        QueryAssembler.TupleMultiply.command) steps a (max B (896*P+multiplyBudget q P)) := by
  obtain ⟨nh,b,entries,htrace,he,hgood,hbytes,hvalue,hframe,hbound,_,_,_,htime,hspace⟩ :=
    HeadSumNative.run q node H E U high owner head g pick hs reps W c hc ids a hq ha
      hshape hmask hbase hW hmatrix hkey hE hH hids hzero hcount hrows hcoeff hcache
      hcapacity hsize hradius width hwidth hZ hP hbit hdegree hhashScale hmarkScale B hlocal hcounter
  have hmasters : QueryMasterFrame a b := ⟨fun j hj =>
    hframe j (List.mem_append_left _ hj)⟩
  have hhead : DenseWord q 853 (headValue q node H E U high owner head g reps ids) b := by
    refine ⟨entries,hbytes,?_,?_⟩
    · simpa only [hq.lifting] using hgood
    · exact Eq.mp (congrArg (fun u => rawValue u q.J q.p.ops.decode entries =
        fiberValue q u node H E U high owner head g reps ids) hq.lifting) hvalue
  have htuple' := htuple.frame (hframe 852 (by decide))
  have hpair' := hpair.frame (hframe 851 (by decide))
  obtain ⟨nm,out,hm,hquery,hpairout,hproduct,hzeroout,hmframe,hout,hf,hregs,hcost,hprefix⟩ :=
    QueryVisitorProgram.multiply_run (hq.frame hmasters) hpair' htuple' hhead hbound hmul
  have hp : QueryExecution.PrefixBound (HeadSumAssembly.head HeadSumAssembly.accepted)
      (nh-1) a B := by
    constructor
    intro elapsed z hle hz
    exact hspace elapsed z (hle.trans (Nat.sub_le _ _)) hz
  have hmp : QueryExecution.PrefixBound QueryAssembler.TupleMultiply.command nm b
      (896*P+multiplyBudget q P) :=
    ⟨fun elapsed z hle hz i => by
      simpa only [multiplyBudget,Nat.add_assoc] using hprefix.bound elapsed z (by omega) hz i⟩
  refine ⟨nh-1+nm,out,he.seq hm,hquery,hpairout,hproduct,hzeroout,
    hmasters.trans hmframe,hout,?_,?_,?_,?_⟩
  · intro i hi
    obtain ⟨hp,h61,h70,h852,h853⟩ := retained_multiply i hi
    exact (hf i hp h61 h70 h852 h853).trans (hframe i (retained_head i hi))
  · intro i hi
    exact (hregs i hi).trans (HeadAcceptedProgram.register_frame htrace i hi)
  · exact Nat.add_le_add ((Nat.sub_le _ _).trans htime)
      (by simpa [multiplyBudget] using Nat.le_of_succ_le hcost)
  · exact QueryExecution.prefix_seq he hm (hp.mono (Nat.le_max_left _ _))
      (hmp.mono (Nat.le_max_right _ _))

/-- These replay words are immutable while the current head product changes. -/
def controlPorts : List (Fin 896) :=
  [836,837,838,839,840,842,843,844,845,846,847,851,869]

private theorem control_retained (i : Fin 896) (hi : i∈controlPorts) :
    i∈retainedPorts := by
  simp only [controlPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

private theorem control_prepare (i : Fin 896) (hi : i∈controlPorts) :
    i∉SignatureHeadPrepare.cleared ∧ i≠864 ∧ i≠865 ∧ i≠175 ∧
      i∉HighQueryAdapter.NativeHeadSelect.changed := by
  simp only [controlPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

/-- Paid key preparation installs the complete actual matrix, correction
mask and factor stream before the fixed head rescan and multiplication. -/
theorem prepare_head_multiply_run {r Q n d M P S Z : ℕ} (q : Factor.Spec r Q n d)
    (node : Fin Q) (H E U : Finset (Fin n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (g : Fin r) (pick : ℕ → Bool)
    (hs : ∀ v : Fin n, v.val ∈ chosenIds pick n ↔ ∃ _ : v ∉ H, head node v = g)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head node v.val) k → Bool)
    (W : List Bool) (c : Fin q.ps.length → Fin (count pick n) → List Bool)
    (hc : ∀ j i, (BinaryArithmetic.toNat (c j i) : ℤ) =
      (BinaryArithmetic.toNat W : ℤ) +
        LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R node j.val
          ((chosenIds pick n).get i))
    (ids : List ℕ) (a : HeadSumProgram.Data)
    (hq : QueryReady q node H high E U M a) (ha : ∀ j, (a.stacks j).length  ≤  P)
    (hshape : a.stacks 651 = List.replicate (count pick n) false)
    (hmask : a.stacks 670 = List.ofFn (fun v : Fin n => pick v.val))
    (hbase : a.stacks 869 = List.ofFn (HighIncidence.glue H high
      (Moments.assemble (fun v : ResidualEmbedding.Free H => head node v.val) reps)))
    (hW : a.stacks 141 = W)
    (hmatrix : a.stacks 847 = OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words
      ((List.ofFn (fun j => List.ofFn (c j))).map OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words))
    (hbits : a.stacks 838 =
      List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
        (chosenIds_bound pick n) (chosenIds_nodup pick n) hs (reps g)))
    (hids : a.stacks 671 = ProgramEncoding.encodeRecords (FactorAssignmentLoop.records ids))
    (hzero : ∀ id j (v : Fin n), v ∈ H →
      PerturbationAssembly.fixedSourceRow q.p q.ps q.packing n id j v = 0)
    (hcount : count pick n+1  ≤  P) (hrows : q.ps.length  ≤  P)
    (hcoeff : ∀ j i, (c j i).length  ≤  P)
    (hcache : 4*M+6  ≤  P)
    (hcapacity : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J  ≤  P)
    (hsize : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
      (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1  ≤  S)
    (hradius : q.p.R+1  ≤  Q) (width : ℕ)
    (hwidth : ∀ f (hf : f < q.rows.length),
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length  ≤  width)
    (hZ : 1  ≤  Z) (hP : P  ≤  Z) (hbit : q.bitWidth  ≤  Z)
    (hdegree : d * baseWidth 3 q.p.t  ≤  Z)
    (hhashScale : ∀ f (hf : f < q.rows.length),
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length  ≤  Z)
    (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0  ≤  Z)
    (B : ℕ)
    (hlocal : 896*P + HeadEvaluationProgram.StagedGate.bodyPolynomial P +
      HeadAcceptedCorrect.budget q P S Z  ≤  B)
    (hcounter : 9*(count pick n+1)+8  ≤  B)
    {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hpair : PairAccumulatorMeaning q pairValue a)
    (htuple : DenseWord q 852 tupleValue a)
    (hmul : FactorProductSpace.byteBound n (baseWidth 3 q.p.t) d q.p.t q.J ≤ P)
    (hprepare : 16*(W.length+count pick n+
      (OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words
        ((List.ofFn (fun j => List.ofFn (c j))).map OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words)).length)+
      AttainedSignatureProgram.cost W
        (List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
          (chosenIds_bound pick n) (chosenIds_nodup pick n) hs (reps g)))
        (List.ofFn (fun j => List.ofFn (c j)))+1 ≤ P)
    (hselect : 11*n+6 ≤ P) :
    ∃ steps b,
      Eval QueryVisitorProgram.evaluateLoadedHead steps a b ∧
      QueryReady q node H high E U M b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 (tupleValue*headValue q node H E U high owner head g reps ids) b ∧
      b.stacks 853=[] ∧ QueryMasterFrame a b ∧ WordBound P b ∧
      (∀ i∈controlPorts,b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      steps ≤ 100*P+200+sumBudget q P S Z B (count pick n)+multiplyBudget q P ∧
      QueryExecution.PrefixBound QueryVisitorProgram.evaluateLoadedHead steps a
        (max (996*P+200) (max B (896*P+multiplyBudget q P))) := by
  let bits := List.ofFn (freeAssignmentEquiv H (fun v => head node v.val) g (chosenIds pick n)
    (chosenIds_bound pick n) (chosenIds_nodup pick n) hs (reps g))
  let rows := List.ofFn (fun j => List.ofFn (c j))
  have hrowlen : ∀ row∈rows,row.length=bits.length := by
    intro row hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    rw [List.length_ofFn]
    simp only [bits, List.length_ofFn]
    rfl
  have hlen : (a.stacks 670).length=(a.stacks 858).length := by
    rw [hmask,hq.outer]
    simp
  obtain ⟨np,kr,sr,hp,hq',hpair',htuple',hmasters,hbound,hptime,hpprefix⟩ :=
    QueryVisitorProgram.prepare_run hq hpair htuple ha W bits rows hW hbits hmatrix hrowlen hlen
      (by simpa only [bits, rows, List.length_ofFn, count] using hprepare)
      (by simpa only [hmask,List.length_ofFn] using hselect)
  let mid := SignatureHeadPrepare.result a kr sr W bits rows
  have hf (i : Fin 896) (hi : i∉SignatureHeadPrepare.cleared) (h864 : i≠864)
      (h865 : i≠865) (h175 : i≠175) (hsel : i∉HighQueryAdapter.NativeHeadSelect.changed) :
      mid.stacks i=a.stacks i :=
    SignatureHeadPrepare.result_frame a kr sr W bits rows hW hbits hmatrix i hi h864 h865 h175 hsel
  obtain ⟨hW',hrows',hkey',hE',hH'⟩ :=
    SignatureHeadPrepare.result_words a kr sr W bits rows hW hbits hmatrix
  have hE'' : mid.stacks 867=HighIncidenceProgram.Restriction.selected true
      (List.ofFn (fun v : Fin n => pick v.val)) (LeafWeightProgram.supportBits ⟨E⟩) := by
    simpa only [hmask,hq.outer,LeafWeightProgram.supportBits] using hE'
  have hH'' : mid.stacks 868=List.replicate (count pick n) true := by
    simpa only [hmask,HeadRepresentativeSemantics.headOrder_highCount] using hH'
  have hids' : mid.stacks 175=ProgramEncoding.encodeRecords (FactorAssignmentLoop.records ids) :=
    (SignatureHeadPrepare.result_factors a kr sr W bits rows hW hbits hmatrix).trans hids
  obtain ⟨nh,out,he,hqo,hpo,hproduct,hzeroout,hmframe,hout,hof,hregs,hcost,hprefix⟩ :=
    head_multiply_run q node H E U high owner head g pick hs reps W c hc ids mid hq' hbound
      ((hf 651 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hshape)
      ((hf 670 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hmask)
      ((hf 869 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hbase)
      hW' hrows' hkey' hE'' hH'' hids' hzero hcount hrows hcoeff hcache hcapacity hsize
      hradius width hwidth hZ hP hbit hdegree hhashScale hmarkScale B hlocal hcounter hpair' htuple' hmul
  have hpref : QueryExecution.PrefixBound SignatureHeadPrepare.command np a (996*P+200) :=
    ⟨fun elapsed z hle hz => hpprefix.bound elapsed z (by omega) hz⟩
  refine ⟨np+nh, out, QueryVisitorProgram.evaluateLoadedHead_eval hp he,
    hqo, hpo, hproduct, hzeroout, hmasters.trans hmframe, hout, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨hc,h864,h865,h175,hs⟩ := control_prepare i hi
    exact (hof i (control_retained i hi)).trans (hf i hc h864 h865 h175 hs)
  · intro i hi
    exact (hregs i hi).trans (SignatureHeadPrepare.result_register_frame a kr sr W bits rows i (by omega))
  · omega
  · exact QueryVisitorProgram.evaluateLoadedHead_prefix hp he
      (hpref.mono (Nat.le_max_left _ _)) (hprefix.mono (Nat.le_max_right _ _))

/-- A generated native matrix is transported only along the actual row-count
identity. Source alignment is pointwise equality of original integer entries;
it is not a supplied coefficient array or execution witness. -/
theorem shifted_source_typed (s : LeafHeadSetupProgram.Native.Inputs) {d : ℕ}
    (q : Factor.Spec s.r s.Q s.n d) (owner : Fin q.ps.length → Fin s.n)
    (nativeOwner : Fin s.D → Fin s.n) (hD : q.ps.length=s.D)
    (howner : ∀ i : Fin s.plans.length,
      (s.plans.get i).1=(nativeOwner (Fin.cast s.plans_length i)).val)
    (hliteral : ∀ j v,
      LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R s.node j v=
      LayoutProducedMatrix.literalNat s.packing nativeOwner s.height.length s.R s.node j v)
    (W : List Bool) (hW : BinaryArithmetic.toNat W=s.offset) (z : ℕ)
    (raw : List (List LayoutMatrixProgram.Pair)) (rows : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (LeafHeadSetupProgram.selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw rows) :
    ∃ c : Fin q.ps.length → Fin (count (predicate s.rows s.low z) s.n) → List Bool,
      rows=List.ofFn (fun j => List.ofFn (c j)) ∧
      ∀ j i,(BinaryArithmetic.toNat (c j i) : ℤ)=(BinaryArithmetic.toNat W : ℤ)+
        LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R s.node
          j.val ((chosenIds (predicate s.rows s.low z) s.n).get i) := by
  let ps : Fin s.D → ℕ × ℕ := fun i => s.plans.get (Fin.cast s.plans_length.symm i)
  have hp : s.plans=List.ofFn ps :=
    (List.ofFn_get s.plans).symm.trans (List.ofFn_congr s.plans_length _)
  have ho : ∀ i,(ps i).1=(nativeOwner i).val := by
    intro i
    simpa only [ps, Fin.cast_cast, Fin.cast_refl, id_eq] using
      howner (Fin.cast s.plans_length.symm i)
  obtain ⟨c,hc,he⟩ := SignatureHeadLoader.native_shiftedMatrix_typed
    s W hW nativeOwner ps hp ho z raw rows hr hy
  refine ⟨fun j => c (Fin.cast hD j),hc.trans (List.ofFn_congr hD.symm _),?_⟩
  intro j i
  rw [hliteral]
  exact he (Fin.cast hD j) i

/-- The last paid clear in the actual multiply leaves the replay scratch
empty, independently of its contents on entry. -/
theorem multiply_scratch {steps : ℕ} {a b : State 40 896}
    (he : Eval QueryAssembler.TupleMultiply.command steps a b) : b.stacks 841=[] := by
  cases he with
  | seq _ htail =>
    cases htail with
    | @seq _ _ _ _ _ mid _ _ hclear =>
      have hc := QueryAssembler.clearPair_eval mid
      have hn := StreamResources.eval_steps_eq (0 : Fin 896) 0 hclear hc
      have ht := compiled_halt_trace hclear (0 : Fin 896) 0
      rw [hn] at ht
      have heq := trace_same_length_unique ht (compiled_halt_trace hc 0 0)
      have hs := congrArg (fun c => c.stacks 841) heq
      exact hs.trans (by
        change (QueryAssembler.clearPairState mid).stacks 841=[]
        rw [QueryAssembler.clearPair_stacks]
        rfl)

/-- The complete fixed one-head visitor finishes in the same paid cleanup. -/
theorem evaluateHead_scratch {steps : ℕ} {a b : State 40 896}
    (he : Eval QueryVisitorProgram.evaluateHead steps a b) : b.stacks 841=[] := by
  unfold QueryVisitorProgram.evaluateHead at he
  cases he with
  | seq _ htail =>
    unfold QueryVisitorProgram.evaluateLoadedHead at htail
    cases htail with
    | seq _ htail =>
      cases htail with
      | seq _ hmul => exact multiply_scratch hmul

/-- These facts identify the actual produced source across all heads. Every
field is an equation about saved source data or its original integer meaning. -/
structure SourceFacts (s : LeafHeadSetupProgram.Native.Inputs) {d : ℕ}
    (q : Factor.Spec s.r s.Q s.n d) (H : Finset (Fin s.n))
    (owner : Fin q.ps.length → Fin s.n) (nativeOwner : Fin s.D → Fin s.n)
    (head : Fin s.Q → Fin s.n → Fin s.r) : Prop where
  dimension : q.ps.length=s.D
  plans_owner : ∀ i : Fin s.plans.length,
    (s.plans.get i).1=(nativeOwner (Fin.cast s.plans_length i)).val
  literal : ∀ j v,
    LayoutProducedMatrix.literalNat q.packing owner q.p.aWord.length q.p.R s.node j v=
    LayoutProducedMatrix.literalNat s.packing nativeOwner s.height.length s.R s.node j v
  selected : ∀ (g : Fin s.r) (v : Fin s.n),
    v.val∈chosenIds (predicate s.rows s.low (s.node.val*s.r+g.val)) s.n ↔
      ∃ _ : v∉H,head s.node v=g
  source_zero : ∀ id j (v : Fin s.n),v∈H →
    PerturbationAssembly.fixedSourceRow q.p q.ps q.packing s.n id j v=0
  rows_length : s.rows.length=s.n+s.N

/-- Fixed numerical envelopes used at every head boundary. These fields are
inequalities in actual source sizes, with no execution or output services. -/
structure HeadBounds (s : LeafHeadSetupProgram.Native.Inputs) {d : ℕ}
    (q : Factor.Spec s.r s.Q s.n d) (M P S Z B L width : ℕ) : Prop where
  load : SignatureHeadLoader.retainedOutputBound s.n s.N s.D s.columnLength L ≤ P
  matrix : QueryVisitorLoadBounds.matrixEnvelope s L ≤ P
  key : QueryVisitorLoadBounds.keyEnvelope s L ≤ P
  select : 11*s.n+6 ≤ P
  count : s.n+1 ≤ P
  rows : q.ps.length ≤ P
  cache : 4*M+6 ≤ P
  capacity : FactorAssignmentLoop.byteBound s.n (baseWidth 3 q.p.t) d q.u q.J ≤ P
  multiply : FactorProductSpace.byteBound s.n (baseWidth 3 q.p.t) d q.p.t q.J ≤ P
  size : 1029*P+99+s.n+s.n*FactorTableProgram.literalRecordBound s.n
    (FactorTableNative.specializedPayloadBound s.n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S
  radius : q.p.R+1 ≤ s.Q
  clause_width : ∀ f (hf : f < q.rows.length),
    ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
      w.literals.length ≤ width
  positive : 1 ≤ Z
  compact : P ≤ Z
  bit : q.bitWidth ≤ Z
  degree : d*baseWidth 3 q.p.t ≤ Z
  hash : ∀ f (hf : f < q.rows.length),
    FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d s.n q.u q.J
      width q.rows[f].length q.digits.length ≤ Z
  marked : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d s.n q.u q.J
    q.markedClause.length 0 0 ≤ Z
  head_local : 896*P+HeadEvaluationProgram.StagedGate.bodyPolynomial P+
    HeadAcceptedCorrect.budget q P S Z ≤ B
  counter : 9*(s.n+1)+8 ≤ B

def factorIds (s : LeafHeadSetupProgram.Native.Inputs) (g : Fin s.r) : List ℕ :=
  LeafHeadFactorsProgram.chosenIds
    (LeafHeadFactorsProgram.predicate s.rows s.n (s.node.val*s.r+g.val)) s.N

/-- The physical compressed representative for this source head. -/
def representativeWord (s : LeafHeadSetupProgram.Native.Inputs) {d : ℕ}
    (q : Factor.Spec s.r s.Q s.n d) (H : Finset (Fin s.n))
    (owner : Fin q.ps.length → Fin s.n) (nativeOwner : Fin s.D → Fin s.n)
    (head : Fin s.Q → Fin s.n → Fin s.r) (facts : SourceFacts s q H owner nativeOwner head)
    (g : Fin s.r)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head s.node v.val) k → Bool) :
    List Bool :=
  List.ofFn (freeAssignmentEquiv H (fun v => head s.node v.val) g
    (chosenIds (predicate s.rows s.low (s.node.val*s.r+g.val)) s.n)
    (chosenIds_bound _ _) (chosenIds_nodup _ _) (facts.selected g) (reps g))

def visitorPorts : List (Fin 896) := [836,837,838,839,840,842,843,844,845,851,869]

private theorem visitor_port (i : Fin 896) (hi : i∈visitorPorts) :
    i∈controlPorts ∧ 768 ≤ i.val ∧ i∉([846,847] : List (Fin 896)) := by
  simp only [visitorPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

/-- Full paid one-head execution. The native loader generates the complete
matrix and selected factor stream inside this same run. The source certificate
contains only the literal source correspondence, and the endpoint bound is
reused unchanged after the exponentially long restricted-fiber scan. -/
theorem evaluateHead_run (s : LeafHeadSetupProgram.Native.Inputs) {d M P S Z B L width B₀ : ℕ}
    (q : Factor.Spec s.r s.Q s.n d) (H E U : Finset (Fin s.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.n) (nativeOwner : Fin s.D → Fin s.n)
    (head : Fin s.Q → Fin s.n → Fin s.r) (facts : SourceFacts s q H owner nativeOwner head)
    (caps : HeadBounds s q M P S Z B L width) (g : Fin s.r)
    (reps : ∀ k, Moments.Head (fun v : ResidualEmbedding.Free H => head s.node v.val) k → Bool)
    (source : LeafHeadSetupProgram.Data) (hsource : LeafHeadSetupProgram.Native.Ready s source)
    (hsourceBound : WordBound B₀ source)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (hwords : LeafHeadSetupProgram.CacheCorrect s.height (LeafHeadSetupProgram.unary s.R) s.width words)
    (a : State 40 896)
    (hmaster : SignatureHeadLoader.MasterFrame (LeafHeadSetupProgram.Native.start s source ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hq : QueryReady q s.node H high E U M a) (ha : WordBound P a)
    {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (hpair : PairAccumulatorMeaning q pairValue a) (htuple : DenseWord q 852 tupleValue a)
    (hbase : a.stacks 869=List.ofFn (HighIncidence.glue H high
      (Moments.assemble (fun v : ResidualEmbedding.Free H => head s.node v.val) reps)))
    (hbits : a.stacks 838=representativeWord s q H owner nativeOwner head facts g reps)
    (haddress : a.stacks 843=LeafHeadSetupProgram.unary (s.node.val*s.r+g.val))
    (hW : (a.stacks 141).length ≤ L) :
    ∃ steps b,Eval QueryVisitorProgram.evaluateHead steps a b ∧
      QueryReady q s.node H high E U M b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 (tupleValue*headValue q s.node H E U high owner head g reps (factorIds s g)) b ∧
      b.stacks 853=[] ∧ b.stacks 841=[] ∧ QueryMasterFrame a b ∧ WordBound P b ∧
      (∀ i∈visitorPorts,b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      steps ≤ QueryVisitorLoad.runEnvelope B₀ P+100*P+200+
        sumBudget q P S Z B (count (predicate s.rows s.low (s.node.val*s.r+g.val)) s.n)+
        multiplyBudget q P ∧
      QueryExecution.PrefixBound QueryVisitorProgram.evaluateHead steps a
        (max (QueryVisitorLoad.runEnvelope B₀ P)
          (max (996*P+200) (max B (896*P+multiplyBudget q P)))) := by
  let z := s.node.val*s.r+g.val
  let pick := predicate s.rows s.low z
  let rep := representativeWord s q H owner nativeOwner head facts g reps
  obtain ⟨rp,rm,rs,raw,rows,nl,hl,hltime,hlbound,hraw,hshift,hlprefix⟩ :=
    QueryVisitorLoad.load_run_polynomial s source hsource B₀ hsourceBound facts.rows_length
      ra rd rc words hwords a hmaster z P L haddress ha hW caps.load
  let mid := QueryVisitorLoad.result s z a rp rm rs raw rows
  have hlmaster : QueryMasterFrame a mid := QueryVisitorLoad.result_query_master_frame ..
  have hhigh (i : Fin 896) (hi : 768 ≤ i.val) (hne : i∉([846,847] : List (Fin 896))) :
      mid.stacks i=a.stacks i := QueryVisitorLoad.result_high_frame s z a rp rm rs raw rows i hi hne
  have hoffset : BinaryArithmetic.toNat (a.stacks 141)=s.offset :=
    SignatureHeadLoader.native_offset s source hsource ra rd rc words _ hmaster
  obtain ⟨c,hrows,hc⟩ := shifted_source_typed s q owner nativeOwner facts.dimension facts.plans_owner
    facts.literal (a.stacks 141) hoffset z raw rows hraw hshift
  have hrep : rep.length=(LeafHeadSetupProgram.selectedHeads s.n s.rows s.low z).length := by
    simp only [rep,representativeWord,List.length_ofFn,LeafHeadSetupProgram.selectedHeads,z]
  obtain ⟨_,hcoeff,hkey⟩ := QueryVisitorLoadBounds.generated_bounds s z L
    (a.stacks 141) rep raw rows hraw hshift hW hrep
  have hco : ∀ j i,(c j i).length ≤ P := by
    intro j i
    have hm : c j i∈List.ofFn (c j) := List.mem_ofFn.mpr ⟨i,rfl⟩
    have hj : List.ofFn (c j)∈rows := by rw [hrows]; exact List.mem_ofFn.mpr ⟨j,rfl⟩
    exact (hcoeff _ hj _ hm).trans caps.matrix
  have hprep : 16*((a.stacks 141).length+count pick s.n+
      (OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words
        ((List.ofFn (fun j => List.ofFn (c j))).map OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words)).length)+
      AttainedSignatureProgram.cost (a.stacks 141)
        (List.ofFn (freeAssignmentEquiv H (fun v => head s.node v.val) g (chosenIds pick s.n)
          (chosenIds_bound pick s.n) (chosenIds_nodup pick s.n) (facts.selected g) (reps g)))
        (List.ofFn (fun j => List.ofFn (c j)))+1 ≤ P := by
    simpa only [hrows,rep,representativeWord,List.length_ofFn,count,z,pick]
      using hkey.trans caps.key
  have hcount : count pick s.n ≤ s.n := HeadIdentifierProgram.count_le pick s.n
  have hshape := QueryVisitorLoad.result_headsize s z a rp rm rs raw rows
  have hmask := QueryVisitorLoad.result_mask_word s z a rp rm rs raw rows
  have hmatrix : mid.stacks 847=OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words
      ((List.ofFn (fun j => List.ofFn (c j))).map OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words) := by
    rw [← hrows]
    exact QueryVisitorLoad.result_matrix ..
  have hids : mid.stacks 671=ProgramEncoding.encodeRecords (FactorAssignmentLoop.records (factorIds s g)) :=
    (QueryVisitorLoad.result_head_outputs s z a rp rm rs raw rows).2.2.2
  obtain ⟨nh,b,he,hqb,hpb,hproduct,hzero,hmframe,hb,hframe,hregs,htime,hprefix⟩ :=
    prepare_head_multiply_run q s.node H E U high owner head g pick (facts.selected g) reps
      (a.stacks 141) c hc (factorIds s g) mid (hq.frame hlmaster) hlbound hshape hmask
      ((hhigh 869 (by decide) (by decide)).trans hbase)
      (QueryVisitorLoad.result_offset ..) hmatrix
      ((hhigh 838 (by decide) (by decide)).trans hbits) hids facts.source_zero
      (by have := caps.count; omega) caps.rows hco caps.cache caps.capacity caps.size caps.radius width caps.clause_width
      caps.positive caps.compact caps.bit caps.degree caps.hash caps.marked B caps.head_local
      (by have := caps.counter; omega)
      (hpair.frame (hhigh 851 (by decide) (by decide)))
      (htuple.frame (hhigh 852 (by decide) (by decide))) caps.multiply hprep caps.select
  have whole : Eval QueryVisitorProgram.evaluateHead (nl+nh) a b := by
    exact hl.seq he
  have hp : QueryExecution.PrefixBound
      (.call (SignatureHeadLoader.programFrom 843)) nl a
      (QueryVisitorLoad.runEnvelope B₀ P) := by
    cases hl with
    | call _ ht =>
      apply call_prefix (SignatureHeadLoader.programFrom 843) ht
      intro elapsed cfg hle htrace i
      exact (word_le_dataBits cfg i).trans (hlprefix elapsed cfg hle htrace)
  refine ⟨nl+nh,b,whole,hqb,hpb,hproduct,hzero,evaluateHead_scratch whole,
    hlmaster.trans hmframe,hb,?_,?_,?_,?_⟩
  · intro i hi
    obtain ⟨hc,h768,hne⟩ := visitor_port i hi
    exact (hframe i hc).trans (hhigh i h768 hne)
  · intro i hi
    exact (hregs i hi).trans (QueryVisitorLoad.result_register_frame s z a rp rm rs raw rows i hi)
  · change nl+nh ≤ QueryVisitorLoad.runEnvelope B₀ P+100*P+200+
      sumBudget q P S Z B (count pick s.n)+multiplyBudget q P
    omega
  · exact QueryVisitorProgram.evaluateHead_prefix hl he
      (hp.mono (Nat.le_max_left _ _)) (hprefix.mono (Nat.le_max_right _ _))

/-- The exact query frame also preserves the real native source/cache bank
needed to reload the next head. -/
theorem source_masterFrame {a b : State 40 896} (hf : QueryMasterFrame a b)
    (base : LeafHeadSetupProgram.Data)
    (hm : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
  constructor
  intro i hi
  have hp : SignatureHeadLoader.lowStacks i∈masterPorts := by
    simp only [SignatureHeadLoader.masters, List.mem_cons,
      List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact (hf.word _ hp).trans (hm.stored i hi)

/-- The offset-word length cap comes from the immutable actual source bank. -/
theorem source_offset_length (s : LeafHeadSetupProgram.Native.Inputs)
    (source : LeafHeadSetupProgram.Data) (B₀ : ℕ) (hb : WordBound B₀ source)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (a : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame (LeafHeadSetupProgram.Native.start s source ra rd rc words)
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    (a.stacks 141).length ≤ B₀ := by
  have hw := SignatureHeadLoader.native_offset_word s source ra rd rc words _ hm
  change a.stacks 141=source.stacks 141 at hw
  rw [hw]
  exact hb 141

/-- Only this fixed polynomial coefficient is shared across heads. The
exponent remains the attained maximum head size supplied by the proved layout. -/
def timeCoefficient {r Q n d : ℕ} (q : Factor.Spec r Q n d) (B₀ P S Z B : ℕ) : ℕ :=
  QueryVisitorLoad.runEnvelope B₀ P+100*P+200+
    (2*(HeadEvaluationProgram.StagedGate.bodyPolynomial P+HeadAcceptedCorrect.budget q P S Z)+
      126*B+54*n+286)+multiplyBudget q P

theorem time_le_max_head {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (B₀ P S Z B h H : ℕ) (hn : h ≤ n) (hH : h ≤ H) :
    QueryVisitorLoad.runEnvelope B₀ P+100*P+200+sumBudget q P S Z B h+multiplyBudget q P ≤
      timeCoefficient q B₀ P S Z B*2^H := by
  have hp : 1 ≤ 2^H := one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))
  have ht : sumBudget q P S Z B h ≤
      (2*(HeadEvaluationProgram.StagedGate.bodyPolynomial P+HeadAcceptedCorrect.budget q P S Z)+
        126*B+54*n+286)*2^H := by
    unfold sumBudget
    exact Nat.mul_le_mul (by omega) (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hH)
  unfold timeCoefficient
  nlinarith

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead
