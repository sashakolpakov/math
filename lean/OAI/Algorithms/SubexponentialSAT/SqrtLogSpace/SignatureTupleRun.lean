import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleWords
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics

/-! Complete runs of the fixed attained-signature controller. The retained
boundary cap is separate from transient prefix storage and measured time. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun

open Classical
open OAI SubexpLiftRing BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource
open SignatureTupleComplete

/-- A single concrete iteration followed by the false guard retains the
same transient bound; the terminal guard introduces no additional storage. -/
theorem one_iteration_prefix (ports : Ports 40) (code : Routines 40 896)
    (steps bound : ℕ) (a b : State 40 896)
    (hactive : a.regs ports.active=true) (halt : b.regs ports.active=false)
    (iteration : Iteration ports code steps a b)
    (hend : WordBound bound b)
    (hbody : QueryExecution.PrefixBound (body ports code) steps a bound) :
    QueryExecution.PrefixBound (loop ports code) (steps+1+1) a bound := by
  have hlast : QueryExecution.PrefixBound (loop ports code) 1 b bound := by
    constructor
    exact StructuredSpace.while_false_stack_bound (body ports code) ports.active b halt hend
      _ _ _ (compiled_site _ 838 838)
  constructor
  exact StructuredSpace.while_true_stack_bound hactive iteration.eval (.while_false halt)
    838 838 hbody.bound hlast.bound _ _ _ (compiled_site _ 838 838)

/-- Paid setup, a proved actual traversal, and the final compiled halt share
one trace and one all-stack prefix bound. -/
theorem setup_traversal_prefix (ports : Ports 40) (code : Routines 40 896)
    (ns nt bound : ℕ) (a b c : State 40 896)
    (setup : Eval code.setup ns a b) (traversal : Traversal ports code nt b c)
    (hs : QueryExecution.PrefixBound code.setup ns a bound)
    (ht : QueryExecution.PrefixBound (loop ports code) nt b bound) :
    QueryExecution.PrefixBound (SignatureTupleProgram.command ports code) (ns+nt+1) a bound := by
  have hseq := QueryExecution.prefix_seq setup traversal.eval hs ht
  constructor
  exact StructuredSpace.compiled_halt_stack_bound (.seq setup traversal.eval) 838 838 hseq.bound

/-- Source port selectors only choose external readback; they do not change
any instruction or stack in an internal command trace. -/
theorem prefix_ports (code : Cmd 40 896) (steps bound : ℕ) (a : State 40 896)
    (h : QueryExecution.PrefixBound code steps a bound) (input output : Fin 896) :
    ∀ p z,p ≤ steps → BitProgram.Trace (compiled code input output) p
      (a.withPC (some (compiled code input output).entry)) z →
      ∀ i,(z.stacks i).length ≤ bound := by
  intro p z hp hz i
  exact h.bound p z hp hz i

/-- Actual zero-head execution visits the unique empty tuple, adds the
readout of the multiplicative unit, returns the original node address and
halts. No callback execution or loader service is an assumption. -/
theorem zero_run (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (hzero : s.input.r=0) (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base)
    (hquery : QueryTupleState.QueryReady q node H high E U P a)
    (hacc : QueryTupleState.PairAccumulatorMeaning q acc a)
    (hPF : 4*P+6 ≤ F)
    (hout : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) ≤ F) :
    ∃ steps b, Eval SignatureTupleComplete.command steps a b ∧
      Rel s F q node H high E U P .halt
        (acc+Dense.readout (1 : Dense (q.p.model.O q.p.t) q.p.t q.J)) b ∧
      steps+1 ≤ QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J F+
        1600*(F+1)+2*eventPolynomial s F+2 ∧
      BitProgram.Trace SignatureTupleComplete.program (steps+1)
        (a.withPC (some SignatureTupleComplete.program.entry)) (b.withPC none) ∧
      QueryExecution.PrefixBound SignatureTupleComplete.command (steps+1) a
        (max (prefixEnvelope s F)
          (896*F+QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J F+1600*(F+1))) := by
  obtain ⟨ns,b,hs,hb,hts,hspaces⟩ := setup_rel_run s F cap q node H high E U P acc a
    hbound hm hz hquery hacc
  rw [enter,dite_eq_left hzero.symm] at hb
  obtain ⟨hactive,nb,c,hit,hc,htb,hspaceb⟩ :=
    zero_leaf_step s F cap q node H high E U P _ acc b hzero hb hPF hout
  have halt := hc.halted.1
  have htr : Traversal controllerPorts routines (nb+1+1) b c :=
    .step hactive hit (.done halt)
  have he : Eval SignatureTupleComplete.command (ns+(nb+1+1)) a c := .seq hs htr.eval
  let D := max (prefixEnvelope s F)
    (896*F+QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J F+1600*(F+1))
  have hFD : F ≤ D := by
    have hp : F ≤ prefixEnvelope s F := by unfold prefixEnvelope; omega
    exact hp.trans (Nat.le_max_left _ _)
  have hbody : QueryExecution.PrefixBound (body controllerPorts routines) nb b D := by
    constructor
    intro p z hp hz i
    exact hspaceb p z (by omega) hz i
  have hend : WordBound D c := fun i => (hc.boundary.wordBound i).trans hFD
  have hl := one_iteration_prefix controllerPorts routines nb D b c hactive halt hit hend hbody
  have hs' : QueryExecution.PrefixBound routines.setup ns a D := by
    constructor
    intro p z hp hz i
    exact (hspaces p z (by omega) hz i).trans (Nat.le_max_left _ _)
  exact ⟨_,c,he,hc,by omega,compiled_halt_trace he 837 851,
    setup_traversal_prefix controllerPorts routines ns (nb+1+1) D a b c hs htr hs' hl⟩

/-- All dimensions used by the arithmetic are read from physical retained
words; their numeric values are bounded by the entry word cap. -/
theorem query_dimensions_le {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d}
    {node : Fin Q} {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {P A : ℕ} {a : State 40 896}
    (hq : QueryTupleState.QueryReady q node H high E U P a) (ha : WordBound A a) :
    n ≤ A ∧ baseWidth 3 q.p.t ≤ A ∧ d ≤ A ∧ q.p.t ≤ A ∧ q.J ≤ A := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa only [hq.ambient,List.length_replicate] using ha 128
  · simpa only [hq.width,q.widthLength] using ha 202
  · simpa only [hq.degree,List.length_replicate] using ha 204
  · simpa only [hq.precision,List.length_replicate] using ha 212
  · simpa only [hq.order,List.length_replicate] using ha 243

/-- The normalized dictionary cap follows from physical input lengths,
rather than from an assumed successful arithmetic output. -/
theorem query_dictionary_cap {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d}
    {node : Fin Q} {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {P A : ℕ} {a : State 40 896}
    (hq : QueryTupleState.QueryReady q node H high E U P a) (ha : WordBound A a) :
    q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) ≤ 10*(A+1)^4 := by
  obtain ⟨hn,hw,hd,ht,hJ⟩ := query_dimensions_le hq ha
  have hdiag : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) ≤       A*A*(2*(A+A+A)+2*(A*A)+2) := by gcongr
  have hp (x : ℕ) : x*x*(2*(x+x+x)+2*(x*x)+2) ≤ 10*(x+1)^4 := by
    nlinarith [sq_nonneg (x*x),sq_nonneg x]
  exact hdiag.trans (hp A)

/-- A sufficient cap for the actual empty tuple path, chosen from physical
entry bounds before running the controller. -/
def emptyRetainedBound (source entry cache : ℕ) : ℕ :=
  retainedEnvelope source (entry+4*cache+6+10*(entry+1)^4)

/-- The zero-head execution needs no supplied retained-space or output-size
contract: both are instantiated from physical input words. -/
theorem zero_run_from_words (s : ProducedSource) (A P : ℕ)
    {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n))
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (hzero : s.input.r=0) (hbound : WordBound A a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base)
    (hquery : QueryTupleState.QueryReady q node H high E U P a)
    (hacc : QueryTupleState.PairAccumulatorMeaning q acc a) :
    let F := emptyRetainedBound s.bound A P
    ∃ steps b, Eval SignatureTupleComplete.command steps a b ∧
      Rel s F q node H high E U P .halt
        (acc+Dense.readout (1 : Dense (q.p.model.O q.p.t) q.p.t q.J)) b ∧
      steps+1 ≤ QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J F+
        1600*(F+1)+2*eventPolynomial s F+2 ∧
      BitProgram.Trace SignatureTupleComplete.program (steps+1)
        (a.withPC (some SignatureTupleComplete.program.entry)) (b.withPC none) ∧
      QueryExecution.PrefixBound SignatureTupleComplete.command (steps+1) a
        (max (prefixEnvelope s F)
          (896*F+QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J F+1600*(F+1))) := by
  dsimp only
  let F := emptyRetainedBound s.bound A P
  have hA : A ≤ F := by dsimp [F,emptyRetainedBound,retainedEnvelope]; omega
  have hP : 4*P+6 ≤ F := by dsimp [F,emptyRetainedBound,retainedEnvelope]; omega
  have hcap := query_dictionary_cap hquery hbound
  have hdict : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) ≤ F := by
    dsimp [F,emptyRetainedBound,retainedEnvelope]
    omega
  exact zero_run s F (retainedEnvelope_cap s _) q node H high E U P acc a hzero
    (fun i => (hbound i).trans hA) hm hz hquery hacc hP hdict

/-- External-facing source resources for the zero-head path use the fixed
program's actual input/output selectors and expose the physical851 result. -/
theorem zero_run_resources (s : ProducedSource) (A P : ℕ)
    {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n))
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (hzero : s.input.r=0) (hbound : WordBound A a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base)
    (hquery : QueryTupleState.QueryReady q node H high E U P a)
    (hacc : QueryTupleState.PairAccumulatorMeaning q acc a) :
    let F := emptyRetainedBound s.bound A P
    ∃ steps b, Eval SignatureTupleComplete.command steps a b ∧
      BitProgram.Trace SignatureTupleComplete.program (steps+1)
        (a.withPC (some SignatureTupleComplete.program.entry)) (b.withPC none) ∧
      QueryTupleState.QueryReady q node H high E U P b ∧
      QueryTupleState.PairAccumulatorMeaning q
        (acc+Dense.readout (1 : Dense (q.p.model.O q.p.t) q.p.t q.J)) b ∧
      WordBound F b ∧ b.stacks 649=unary s.base ∧
      steps+1 ≤ QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J F+
        1600*(F+1)+2*eventPolynomial s F+2 ∧
      ∀ p z,p ≤ steps+1 → BitProgram.Trace SignatureTupleComplete.program p
        (a.withPC (some SignatureTupleComplete.program.entry)) z →
        ∀ i,(z.stacks i).length ≤ max (prefixEnvelope s F)
          (896*F+QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J F+1600*(F+1)) := by
  obtain ⟨steps,b,he,hb,ht,htrace,hspace⟩ :=
    zero_run_from_words s A P q node H high E U acc a hzero hbound hm hz hquery hacc
  exact ⟨steps,b,he,htrace,hb.query,hb.accumulator,hb.boundary.wordBound,hb.halted.2,ht,
    prefix_ports SignatureTupleComplete.command _ _ a hspace 837 851⟩

/-- Determinism transfers a locally exhibited iteration's bound to every
actual body derivation used by the compiled while-loop prefix theorem. -/
theorem traversal_prefix_of_iterations (ports : Ports 40) (code : Routines 40 896)
    (I : State 40 896 → Prop) (D : ℕ)
    (hbound : ∀ a,I a → WordBound D a)
    (hrealized : ∀ a,I a → a.regs ports.active=true → ∃ steps b,
      Iteration ports code steps a b ∧ I b ∧
        QueryExecution.PrefixBound (body ports code) (steps+1) a D)
    {steps : ℕ} {a b : State 40 896} (ht : Traversal ports code steps a b) (ha : I a) :
    QueryExecution.PrefixBound (loop ports code) steps a D := by
  have preserve : ∀ n a b,Eval (body ports code) n a b → I a →
      a.regs ports.active=true → I b ∧ QueryExecution.PrefixBound (body ports code) (n+1) a D := by
    intro n a b he ha active
    obtain ⟨n',b',hit,hb,hp⟩ := hrealized a ha active
    have htime := StreamResources.eval_steps_eq (0 : Fin 896) 0 he hit.eval
    have hout := he.final_unique (0 : Fin 896) hit.eval
    subst n'
    subst b'
    exact ⟨hb,hp⟩
  constructor
  apply traversal_stack_bound ports code 838 838 I D hbound
  · intro n a b he ha active
    exact (preserve n a b he ha active).1
  · intro n a b he ha active elapsed z hprefix hz i
    exact (preserve n a b he ha active).2.bound elapsed z (by omega) hz i
  · exact ht
  · exact ha

/-- The enriched cursor relation supplies a uniform whole-loop prefix
invariant from actual locally realized steps; no traversal-time term is used
as a space bound. -/
theorem rel_loop_prefix (s : ProducedSource) (F D leafCost : ℕ) (hFD : F ≤ D)
    {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
    (value : Prefix (Representatives s.key) s.input.r → Truncated (q.p.model.O q.p.t) q.J)
    (hstep : ∀ event before after acc a,Step s.key s.input.r event before after →
      Rel s F q node H high E U P before acc a →
      a.regs controllerPorts.active=true ∧ ∃ steps b,
        Iteration controllerPorts routines steps a b ∧
        Rel s F q node H high E U P after (acc+callbackWeight s.key s.input.r value event) b ∧
        steps+1 ≤ costWeight s.key s.input.r (eventPolynomial s F) leafCost event ∧
        QueryExecution.PrefixBound (body controllerPorts routines) (steps+1) a D)
    {cursor : Cursor s.key s.input.r} {acc : Truncated (q.p.model.O q.p.t) q.J}
    {steps : ℕ} {a b : State 40 896} (ht : Traversal controllerPorts routines steps a b)
    (ha : Rel s F q node H high E U P cursor acc a) :
    QueryExecution.PrefixBound (loop controllerPorts routines) steps a D := by
  let I : State 40 896 → Prop := fun state => ∃ cursor total,Rel s F q node H high E U P cursor total state
  apply traversal_prefix_of_iterations controllerPorts routines I D
  · intro state hstate i
    obtain ⟨cursor,total,hstate⟩ := hstate
    exact (hstate.boundary.wordBound i).trans hFD
  · intro state hstate active
    obtain ⟨cursor,total,hstate⟩ := hstate
    obtain ⟨event,after,hnext⟩ := hstate.enabled active
    obtain ⟨_,n,out,hit,hout,_,hprefix⟩ := hstep event cursor after total state hnext hstate
    exact ⟨n,out,hit,⟨after,_,hout⟩,hprefix⟩
  · exact ht
  · exact ⟨_,_,ha⟩

/-- The mathematical sum over attained tuples, with its finite instance fixed
before specialization to a concrete integer signature. This is proof-side data;
the controller stores only one attained path. -/
noncomputable def tupleTotal {N : ℕ → ℕ} {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ)
    {M : Type*} [AddCommMonoid M] (value : Prefix (Representatives key) levels → M) : M :=
  ∑ ancestors, value ancestors

/-- The mathematical attained-prefix count, independent of runtime storage. -/
noncomputable def tupleCount {N : ℕ → ℕ} {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (N d) → κ d) (levels : ℕ) : ℕ :=
  prefixCount (fun depth => Fintype.card (Representatives key depth)) levels

/-- Composition support for the already fixed controller. Every supplied
clause is an actual local body proof, including its SAME boundary and separate
prefix bound. The concrete positive endpoint must instantiate these clauses
with the visitor, loader, scanner and return proofs. -/
theorem assemble_realized_steps (s : ProducedSource) (F D leafCost hmax : ℕ)
    (cap : RetainedCap s F) (hFD : F ≤ D) (hsetupD : prefixEnvelope s F ≤ D)
    (hheads : ∀ depth<s.input.r,s.headSize depth ≤ hmax)
    {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
    (value : Prefix (Representatives s.key) s.input.r → Truncated (q.p.model.O q.p.t) q.J)
    (hstep : ∀ event before after acc a,Step s.key s.input.r event before after →
      Rel s F q node H high E U P before acc a →
      a.regs controllerPorts.active=true ∧ ∃ steps b,
        Iteration controllerPorts routines steps a b ∧
        Rel s F q node H high E U P after (acc+callbackWeight s.key s.input.r value event) b ∧
        steps+1 ≤ costWeight s.key s.input.r (eventPolynomial s F) leafCost event ∧
        QueryExecution.PrefixBound (body controllerPorts routines) (steps+1) a D)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base)
    (hquery : QueryTupleState.QueryReady q node H high E U P a)
    (hacc : QueryTupleState.PairAccumulatorMeaning q acc a) :
    ∃ steps b, Eval SignatureTupleComplete.command steps a b ∧
      Rel s F q node H high E U P .halt (acc+tupleTotal s.key s.input.r value) b ∧
      steps+1 ≤ eventPolynomial s F+
        (2*eventPolynomial s F)*s.input.r*
          tupleCount s.key s.input.r*4^hmax+
        tupleCount s.key s.input.r*leafCost+2 ∧
      BitProgram.Trace SignatureTupleComplete.program (steps+1)
        (a.withPC (some SignatureTupleComplete.program.entry)) (b.withPC none) ∧
      QueryExecution.PrefixBound SignatureTupleComplete.command (steps+1) a D := by
  obtain ⟨ns,b,hs,hb,hts,hspaces⟩ := setup_rel_run s F cap q node H high E U P acc a
    hbound hm hz hquery hacc
  have localStep : ∀ event before after acc a,Step s.key s.input.r event before after →
      Rel s F q node H high E U P before acc a →
      a.regs controllerPorts.active=true ∧ ∃ steps b,
        Iteration controllerPorts routines steps a b ∧
        Rel s F q node H high E U P after (acc+callbackWeight s.key s.input.r value event) b ∧
        steps+1 ≤ costWeight s.key s.input.r (eventPolynomial s F) leafCost event := by
    intro event before after acc a he ha
    obtain ⟨active,steps,b,hit,hb,ht,_⟩ := hstep event before after acc a he ha
    exact ⟨active,steps,b,hit,hb,ht⟩
  obtain ⟨nt,c,htr,hc,htt⟩ := native_complete_bounded s.headSize s.key s.input.r
    (eventPolynomial s F) leafCost hmax hheads value controllerPorts routines
    (Rel s F q node H high E U P) localStep (fun _ _ h => h.halted.1) acc b hb
  have hpLoop := rel_loop_prefix s F D leafCost hFD q node H high E U P value hstep htr hb
  have hpSetup : QueryExecution.PrefixBound routines.setup ns a D := by
    constructor
    intro p z hp hz i
    exact (hspaces p z (by omega) hz i).trans hsetupD
  have he : Eval SignatureTupleComplete.command (ns+nt) a c := .seq hs htr.eval
  have combine (i t p work leaf : ℕ) (hi : i+1 ≤ p) (ht : t ≤ work+leaf+1) :
      i+t+1 ≤ p+work+leaf+2 := by omega
  exact ⟨ns+nt,c,he,hc,combine _ _ _ _ _ hts htt,compiled_halt_trace he 837 851,
    setup_traversal_prefix controllerPorts routines ns nt D a b c hs htr hpSetup hpLoop⟩

/-- The paid setup preserves every retained query word, including the node
and finite-difference pair banks. -/
theorem setup_masterFrame (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (a : State 40 896) (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base) {steps : ℕ} {b : State 40 896}
    (he : Eval routines.setup steps a b) : QueryTupleState.QueryMasterFrame a b := by
  obtain ⟨n,c,hc,_,_,_,hf⟩ := setup_run s F cap a hbound hm hz
  have hout := he.final_unique (0 : Fin 896) hc
  subst c
  exact query_frame_of_persistent a b hf

/-- The actual nonleaf controller derivation retains all query masters.
The state is identified with the proved loader/scanner/frame implementation. -/
theorem nonleaf_iteration_masterFrame (s : ProducedSource) (F leafCost : ℕ)
    (cap : RetainedCap s F) (event : Event s.key s.input.r)
    (before after : Cursor s.key s.input.r) {a b : State 40 896} {steps : ℕ}
    (step : Step s.key s.input.r event before after) (ha : Boundary s F before a)
    (hnoleaf : ∀ ancestors,event≠Event.leaf ancestors)
    (hit : Iteration controllerPorts routines steps a b) :
    QueryTupleState.QueryMasterFrame a b := by
  obtain ⟨_,n,c,hc,_,_,_,hf⟩ := nonleaf_step s F leafCost cap event before after a step ha hnoleaf
  have hout := hit.eval.final_unique (0 : Fin 896) hc.eval
  subst c
  exact query_frame_of_persistent a b hf

/-- Relational traversal composes exact physical frames without storing a
trace or a family of states at runtime. -/
theorem traversal_masterFrame (ports : Ports 40) (code : Routines 40 896)
    (I : State 40 896 → Prop)
    (hstep : ∀ n a b,I a → a.regs ports.active=true → Iteration ports code n a b →
      I b ∧ QueryTupleState.QueryMasterFrame a b)
    {steps : ℕ} {a b : State 40 896} (ht : Traversal ports code steps a b) (ha : I a) :
    QueryTupleState.QueryMasterFrame a b := by
  induction ht with
  | done _ => exact .refl _
  | step active hit _ ih =>
    obtain ⟨hb,hf⟩ := hstep _ _ _ ha active hit
    exact hf.trans (ih hb)

/-- The zero-head execution also preserves all84 immutable query words;
in particular the next pair can reuse850 and832..835 verbatim. -/
theorem zero_run_masterFrame (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (hzero : s.input.r=0) (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base)
    (hquery : QueryTupleState.QueryReady q node H high E U P a)
    (hacc : QueryTupleState.PairAccumulatorMeaning q acc a) (hPF : 4*P+6 ≤ F)
    (hout : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) ≤ F)
    {steps : ℕ} {out : State 40 896} (he : Eval SignatureTupleComplete.command steps a out) :
    QueryTupleState.QueryMasterFrame a out := by
  obtain ⟨ns,b,hs,hb,_,_⟩ := setup_rel_run s F cap q node H high E U P acc a
    hbound hm hz hquery hacc
  have hsetup := setup_masterFrame s F cap a hbound hm hz hs
  rw [enter,dite_eq_left hzero.symm] at hb
  cases hboundary : hb.boundary with
  | leaf hl =>
    have hreps : b.stacks 837=[] := by
      change b.stacks (tupleStacks 1)=[]
      rw [hl.representatives]
      simp only [representativeFrames,representativeWords,hzero,List.ofFn_zero,
        List.reverse_nil,suspendedFrames,List.flatMap_nil]
    obtain ⟨nv,c,hvisit,_,_,hc,hmasters,hframes,hregs,hcurrent,h649,_,_⟩ :=
      QueryVisitorProgram.visitor_empty hb.query hb.accumulator hl.bound hPF hreps hout
    have hleaf := leafBoundary_frame s F _ b c hl hc hmasters hframes hregs hcurrent
      (fun _ => h649)
    obtain ⟨na,e,hasc,hhalt,_,_,hframe⟩ := ascend_leaf s F cap _ c hleaf
    have hterminal : Boundary s F Cursor.halt e := by
      simpa only [leave_zero s.headSize s.key s.input.r hzero] using hhalt
    have hflag : e.regs controllerPorts.active=false := by
      cases hterminal with
      | halt h => exact h.active
    have hit : Iteration controllerPorts routines (nv+na+1) b e :=
      .leaf hl.leaf hvisit hasc
    have ht : Traversal controllerPorts routines (nv+na+1+1+1) b e :=
      .step (n := nv+na+1) (m := 1) hl.active hit (.done hflag)
    have hall : Eval SignatureTupleComplete.command (ns+(nv+na+1+1+1)) a e :=
      .seq hs ht.eval
    have hfinal := he.final_unique (0 : Fin 896) hall
    subst e
    exact hsetup.trans (hmasters.trans (query_frame_of_persistent c out hframe))

/-- Decode exactly the bounded numeric representative already retained by
the controller, in the actual loader's increasing ambient-coordinate order. -/
def emittedRepresentatives (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (ancestors : Prefix (Representatives s.key) s.input.r) (g : Fin s.input.r) :
    Moments.Head (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g → Bool :=
  (BucketTupleProgram.Concrete.freeAssignmentEquiv H
    (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g
    (selectedHeads s.input.n s.input.rows s.input.low (s.base+g.val))
    (HeadIdentifierProgram.chosenIds_bound _ _) (HeadIdentifierProgram.chosenIds_nodup _ _)
    (facts.selected g)).symm (AttainedSignatures.assignmentEquiv (s.headSize g.val) (ancestors g).val)

/-- No new representative is selected while reconstructing a leaf. -/
theorem emitted_word (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H : Finset (Fin s.input.n)) (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (ancestors : Prefix (Representatives s.key) s.input.r) (g : Fin s.input.r) :
    QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g
      (emittedRepresentatives s q H owner head facts ancestors)=
        ExecCNFTupleEnumeration.fixedBits (s.headSize g.val) (ancestors g).val.val := by
  unfold QueryVisitorHead.representativeWord emittedRepresentatives
  let e : (Moments.Head (fun v : ResidualEmbedding.Free H =>
      head s.input.node v.val) g → Bool) ≃ (Fin (s.headSize g.val) → Bool) :=
    BucketTupleProgram.Concrete.freeAssignmentEquiv H
    (fun v : ResidualEmbedding.Free H => head s.input.node v.val) g
    (selectedHeads s.input.n s.input.rows s.input.low (s.base+g.val))
    (HeadIdentifierProgram.chosenIds_bound _ _) (HeadIdentifierProgram.chosenIds_nodup _ _)
    (facts.selected g)
  change List.ofFn (e (e.symm (AttainedSignatures.assignmentEquiv
    (s.headSize g.val) (ancestors g).val)))=_
  rw [e.apply_symm_apply]
  exact AttainedSignatures.assignment_word (s.headSize g.val) (ancestors g).val

/-- Additive readout is applied after the completed product of actual
restricted full-signature head sums. -/
def emittedValue (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (ancestors : Prefix (Representatives s.key) s.input.r) : Truncated (q.p.model.O q.p.t) q.J :=
  Dense.readout (∏ g : Fin s.input.r,
    QueryVisitorHead.headValue q s.input.node H E U high owner head g
      (emittedRepresentatives s q H owner head facts ancestors) (QueryVisitorHead.factorIds s.input g))

/-- An attained leaf now invokes the actual two-pass visitor and the actual
return controller. All arithmetic and head-loading services are instantiated. -/
theorem leaf_step (s : ProducedSource) {d M F S Z B width height : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : RetainedCap s F) (hpositive : 0<s.input.r)
    (hheads : ∀ depth<s.input.r,s.headSize depth ≤ height)
    (ancestors : Prefix (Representatives s.key) s.input.r)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (ha : Rel s F q s.input.node H high E U M (.leaf ancestors) acc a) :
    a.regs controllerPorts.active=true ∧ ∃ steps b,
      Iteration controllerPorts routines steps a b ∧
      Rel s F q s.input.node H high E U M (leave s.key s.input.r s.input.r le_rfl ancestors)
        (acc+emittedValue s q H E U high owner head facts ancestors) b ∧
      steps+1 ≤ QueryVisitorSemantics.visitorCost s q F S Z B height+eventPolynomial s F ∧
      QueryExecution.PrefixBound (body controllerPorts routines) (steps+1) a
        (max (prefixEnvelope s F) (QueryVisitorSemantics.visitorSpace s q F B)) ∧
      QueryTupleState.QueryMasterFrame a b := by
  cases hboundary : ha.boundary with
  | leaf hl =>
    have hreps : a.stacks 837=suspendedFrames (List.ofFn (fun g =>
        QueryVisitorHead.representativeWord s.input q H owner s.owner head facts g
          (emittedRepresentatives s q H owner head facts ancestors))).reverse := by
      rw [show a.stacks 837=representativeFrames s.headSize s.key s.input.r ancestors
        from hl.representatives]
      simp only [representativeFrames,representativeWords,emitted_word]
    obtain ⟨nv,b,hvisit,hqr,hacc,hframe,hb,hports,hregs,hcurrent,htv,hpv⟩ :=
      QueryVisitorSemantics.visitor_run s q H E U high owner head facts caps
        (emittedRepresentatives s q H owner head facts ancestors)
        (fun g => hheads g.val g.isLt) a ha.query ha.accumulator hl.bound hl.masters
        hreps hl.address (hl.cleared 838 (by decide))
    have hleaf := leafBoundary_frame s F ancestors a b hl hb hframe hports hregs hcurrent
      (fun hz => by omega)
    obtain ⟨na,c,hasc,hc,hta,hpa,hfa⟩ := ascend_leaf s F cap ancestors b hleaf
    have hframea := query_frame_of_persistent b c hfa
    have hr : Rel s F q s.input.node H high E U M
        (leave s.key s.input.r s.input.r le_rfl ancestors)
        (acc+emittedValue s q H E U high owner head facts ancestors) c :=
      ⟨hc,hqr.frame hframea,hacc.frame (hfa 851 ⟨by decide,by decide,by decide⟩)⟩
    refine ⟨hl.active,nv+na+1,c,Iteration.leaf hl.leaf hvisit hasc,hr,by omega,?_,
      hframe.trans hframea⟩
    constructor
    unfold routines
    apply SignatureTupleBranchSpace.leaf_body_prefix_bound loadHead QueryVisitorProgram.visitor
      a b c nv na _ hl.leaf hvisit hasc
    · intro elapsed cfg he ht i
      exact (hpv.bound elapsed cfg (by omega) ht i).trans (Nat.le_max_right _ _)
    · intro elapsed cfg he ht i
      exact (hpa elapsed cfg (by omega) ht i).trans (Nat.le_max_left _ _)

def leafCost (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (F S Z B height : ℕ) : ℕ :=
  QueryVisitorSemantics.visitorCost s q F S Z B height+eventPolynomial s F

def runSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (F B : ℕ) : ℕ :=
  max (prefixEnvelope s F) (QueryVisitorSemantics.visitorSpace s q F B)

/-- Every semantic event is implemented by the fixed concrete controller.
No local evaluator or successful-run premise remains in this theorem. -/
theorem actual_step (s : ProducedSource) {d M F S Z B width height : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : RetainedCap s F) (hpositive : 0<s.input.r)
    (hheads : ∀ depth<s.input.r,s.headSize depth ≤ height)
    (event : Event s.key s.input.r) (before after : Cursor s.key s.input.r)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (step : Step s.key s.input.r event before after)
    (ha : Rel s F q s.input.node H high E U M before acc a) :
    a.regs controllerPorts.active=true ∧ ∃ steps b,
      Iteration controllerPorts routines steps a b ∧
      Rel s F q s.input.node H high E U M after
        (acc+callbackWeight s.key s.input.r (emittedValue s q H E U high owner head facts) event) b ∧
      steps+1 ≤ costWeight s.key s.input.r (eventPolynomial s F) (leafCost s q F S Z B height) event ∧
      QueryExecution.PrefixBound (body controllerPorts routines) (steps+1) a (runSpace s q F B) ∧
      QueryTupleState.QueryMasterFrame a b := by
  by_cases hleaf : ∃ ancestors,event=Event.leaf ancestors
  · obtain ⟨ancestors,rfl⟩ := hleaf
    cases step with
    | leaf ancestors =>
      exact leaf_step s q H E U high owner head facts caps cap hpositive hheads ancestors acc a ha
  · have hnon : ∀ ancestors,event≠Event.leaf ancestors := by
      intro ancestors he
      exact hleaf ⟨ancestors,he⟩
    obtain ⟨hactive,steps,b,hit,hb,ht,hp⟩ :=
      nonleaf_rel_step s F (leafCost s q F S Z B height) cap q s.input.node H high E U M
        (emittedValue s q H E U high owner head facts) event before after acc a step ha hnon
    refine ⟨hactive,steps,b,hit,hb,ht,?_,?_⟩
    · constructor
      intro elapsed cfg helapsed htrace i
      exact (hp elapsed cfg helapsed htrace i).trans (Nat.le_max_left _ _)
    · exact nonleaf_iteration_masterFrame s F (leafCost s q F S Z B height)
        cap event before after step ha.boundary hnon hit

/-- The complete positive-depth run executes each attained tuple once.
The actual84-master frame, count-accumulator meaning, time and every source
prefix all refer to this same fixed program execution. Numerical/source
certificates are instantiated by the actual produced-input constructors. -/
theorem positive_run_resources (s : ProducedSource) {d M F S Z B width height : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : RetainedCap s F) (hpositive : 0<s.input.r)
    (hheads : ∀ depth<s.input.r,s.headSize depth ≤ height)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base)
    (hquery : QueryTupleState.QueryReady q s.input.node H high E U M a)
    (hacc : QueryTupleState.PairAccumulatorMeaning q acc a) :
    ∃ steps b, Eval SignatureTupleComplete.command steps a b ∧
      BitProgram.Trace SignatureTupleComplete.program (steps+1)
        (a.withPC (some SignatureTupleComplete.program.entry)) (b.withPC none) ∧
      QueryTupleState.QueryReady q s.input.node H high E U M b ∧
      QueryTupleState.PairAccumulatorMeaning q
        (acc+tupleTotal s.key s.input.r (emittedValue s q H E U high owner head facts)) b ∧
      WordBound F b ∧ b.stacks 649=unary s.base ∧ QueryTupleState.QueryMasterFrame a b ∧
      steps+1 ≤ eventPolynomial s F+(2*eventPolynomial s F)*s.input.r*
        tupleCount s.key s.input.r*4^height+tupleCount s.key s.input.r*leafCost s q F S Z B height+2 ∧
      ∀ elapsed cfg,elapsed ≤ steps+1 → BitProgram.Trace SignatureTupleComplete.program elapsed
        (a.withPC (some SignatureTupleComplete.program.entry)) cfg →
        ∀ i,(cfg.stacks i).length ≤ runSpace s q F B := by
  let value := emittedValue s q H E U high owner head facts
  let cost := leafCost s q F S Z B height
  have localStep : ∀ event before after acc a,Step s.key s.input.r event before after →
      Rel s F q s.input.node H high E U M before acc a →
      a.regs controllerPorts.active=true ∧ ∃ steps b,
        Iteration controllerPorts routines steps a b ∧
        Rel s F q s.input.node H high E U M after
          (acc+callbackWeight s.key s.input.r value event) b ∧
        steps+1 ≤ costWeight s.key s.input.r (eventPolynomial s F) cost event := by
    intro event before after acc a he ha
    obtain ⟨active,steps,b,hit,hb,ht,_,_⟩ :=
      actual_step s q H E U high owner head facts caps cap hpositive hheads event before after acc a he ha
    exact ⟨active,steps,b,hit,hb,ht⟩
  obtain ⟨ns,b,hs,hb,hts,hspaces⟩ := setup_rel_run s F cap q s.input.node H high E U M acc a
    hbound hm hz hquery hacc
  obtain ⟨nt,c,htr,hc,htt⟩ := native_complete_bounded s.headSize s.key s.input.r
    (eventPolynomial s F) cost height hheads value controllerPorts routines
    (Rel s F q s.input.node H high E U M) localStep (fun _ _ h => h.halted.1) acc b hb
  have hFD : F ≤ runSpace s q F B := by
    have hp : F ≤ prefixEnvelope s F := by unfold prefixEnvelope; omega
    exact hp.trans (Nat.le_max_left _ _)
  have hpLoop := rel_loop_prefix s F (runSpace s q F B) cost hFD q s.input.node H high E U M value
    (fun event before after acc a he ha => by
      obtain ⟨active,steps,b,hit,hb,ht,hp,_⟩ :=
        actual_step s q H E U high owner head facts caps cap hpositive hheads event before after acc a he ha
      exact ⟨active,steps,b,hit,hb,ht,hp⟩) htr hb
  let I : State 40 896 → Prop := fun state =>
    ∃ cursor total,Rel s F q s.input.node H high E U M cursor total state
  have hpreserve : ∀ steps a b,I a → a.regs controllerPorts.active=true →
      Iteration controllerPorts routines steps a b → I b ∧ QueryTupleState.QueryMasterFrame a b := by
    intro steps a b hI hactive hit
    obtain ⟨cursor,total,ha⟩ := hI
    obtain ⟨event,after,he⟩ := ha.enabled hactive
    obtain ⟨_,n,out,hi,ho,_,_,hf⟩ :=
      actual_step s q H E U high owner head facts caps cap hpositive hheads event cursor after total a he ha
    have heq := hit.eval.final_unique (0 : Fin 896) hi.eval
    subst out
    exact ⟨⟨after,_,ho⟩,hf⟩
  have hloopFrame := traversal_masterFrame controllerPorts routines I hpreserve htr ⟨_,_,hb⟩
  have hpSetup : QueryExecution.PrefixBound routines.setup ns a (runSpace s q F B) := by
    constructor
    intro elapsed cfg he ht i
    exact (hspaces elapsed cfg (by omega) ht i).trans (Nat.le_max_left _ _)
  have he : Eval SignatureTupleComplete.command (ns+nt) a c := .seq hs htr.eval
  have hp := setup_traversal_prefix controllerPorts routines ns nt (runSpace s q F B)
    a b c hs htr hpSetup hpLoop
  have combine (i t p work leaf : ℕ) (hi : i+1 ≤ p) (ht : t ≤ work+leaf+1) :
      i+t+1 ≤ p+work+leaf+2 := by omega
  exact ⟨ns+nt,c,he,compiled_halt_trace he 837 851,hc.query,hc.accumulator,
    hc.boundary.wordBound,hc.halted.2,(setup_masterFrame s F cap a hbound hm hz hs).trans hloopFrame,
    combine _ _ _ _ _ hts htt,prefix_ports SignatureTupleComplete.command _ _ a hp 837 851⟩

def runTime (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (F S Z B height : ℕ) : ℕ :=
  eventPolynomial s F+(2*eventPolynomial s F)*s.input.r*tupleCount s.key s.input.r*4^height+
    tupleCount s.key s.input.r*leafCost s q F S Z B height+2

/-- The empty-head path uses its actual unit-addition prefix bound. Both
branches retain the same F and have a single polynomial transient cap. -/
def completeSpace (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (F B : ℕ) : ℕ :=
  max (runSpace s q F B)
    (896*F+QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J F+1600*(F+1))

theorem zero_total (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (hz : s.input.r=0) :
    tupleTotal s.key s.input.r (emittedValue s q H E U high owner head facts)=
      Dense.readout (1 : Dense (q.p.model.O q.p.t) q.p.t q.J) := by
  let : IsEmpty (Fin s.input.r) := ⟨fun i => by have := i.isLt; omega⟩
  have hv (ancestors : Prefix (Representatives s.key) s.input.r) :
      emittedValue s q H E U high owner head facts ancestors=
        Dense.readout (1 : Dense (q.p.model.O q.p.t) q.p.t q.J) := by
    unfold emittedValue
    simp
  unfold tupleTotal
  simp only [hv]
  simp

theorem tupleCount_zero {N : ℕ → ℕ} {κ : ℕ → Type*}
    (key : (depth : ℕ) → Fin (N depth) → κ depth) : tupleCount key 0=1 := by
  simp only [tupleCount,prefixCount,Finset.range_zero,Finset.prod_empty]

/-- The common event budget specializes to exactly the paid empty-tuple
execution, including its return and terminal guard. -/
theorem zero_runTime (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (F S Z B height : ℕ)
    (hzero : s.input.r=0) :
    QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J F+
      1600*(F+1)+2*eventPolynomial s F+2=runTime s q F S Z B height := by
  have hk : tupleCount s.key s.input.r=1 :=
    (congrArg (tupleCount s.key) hzero).trans (tupleCount_zero s.key)
  have arithmetic (p r K power tail rest : ℕ) (hr : r=0) (hK : K=1) :
      tail+2*p+2=p+(2*p)*r*K*power+K*(tail+rest*r+p)+2 := by
    subst r
    subst K
    omega
  exact arithmetic (eventPolynomial s F) s.input.r (tupleCount s.key s.input.r) (4^height)
    (QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J F+1600*(F+1))
    (QueryVisitorSemantics.baselineCost s F+QueryVisitorSemantics.evaluationCost s q F S Z B height+20)
    hzero hk

/-- Unified actual tuple execution, including the unique empty tuple.
The exact same851 meaning and retained cap support repeated finite-difference
pairs; all master words, including850 and832..835, are preserved. -/
theorem run_resources (s : ProducedSource) {d M F S Z B width height : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : RetainedCap s F) (hheads : ∀ depth<s.input.r,s.headSize depth ≤ height)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base)
    (hquery : QueryTupleState.QueryReady q s.input.node H high E U M a)
    (hacc : QueryTupleState.PairAccumulatorMeaning q acc a) :
    ∃ steps b, Eval SignatureTupleComplete.command steps a b ∧
      BitProgram.Trace SignatureTupleComplete.program (steps+1)
        (a.withPC (some SignatureTupleComplete.program.entry)) (b.withPC none) ∧
      QueryTupleState.QueryReady q s.input.node H high E U M b ∧
      QueryTupleState.PairAccumulatorMeaning q
        (acc+tupleTotal s.key s.input.r (emittedValue s q H E U high owner head facts)) b ∧
      WordBound F b ∧ b.stacks 649=unary s.base ∧ QueryTupleState.QueryMasterFrame a b ∧
      steps+1 ≤ runTime s q F S Z B height ∧
      ∀ elapsed cfg,elapsed ≤ steps+1 → BitProgram.Trace SignatureTupleComplete.program elapsed
        (a.withPC (some SignatureTupleComplete.program.entry)) cfg →
        ∀ i,(cfg.stacks i).length ≤ completeSpace s q F B := by
  by_cases hzero : s.input.r=0
  · obtain ⟨steps,b,he,hb,ht,htrace,hspace⟩ :=
      zero_run s F cap q s.input.node H high E U M acc a hzero hbound hm hz hquery hacc
        caps.cache caps.multiply
    have hframe := zero_run_masterFrame s F cap q s.input.node H high E U M acc a hzero
      hbound hm hz hquery hacc caps.cache caps.multiply he
    have htotal := zero_total s q H E U high owner head facts hzero
    have htime := zero_runTime s q F S Z B height hzero
    refine ⟨steps,b,he,htrace,hb.query,?_,hb.boundary.wordBound,hb.halted.2,hframe,
      ht.trans htime.le,?_⟩
    · simpa only [htotal] using hb.accumulator
    · intro elapsed cfg helapsed htrace i
      apply (prefix_ports SignatureTupleComplete.command _ _ a hspace 837 851
        elapsed cfg helapsed htrace i).trans
      apply max_le
      · exact (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
      · exact Nat.le_max_right _ _
  · obtain ⟨steps,b,he,htrace,hqr,hacc,hb,h649,hframe,ht,hspace⟩ :=
      positive_run_resources s q H E U high owner head facts caps cap (Nat.pos_of_ne_zero hzero)
        hheads acc a hbound hm hz hquery hacc
    exact ⟨steps,b,he,htrace,hqr,hacc,hb,h649,hframe,ht,fun elapsed cfg helapsed htrace i =>
      (hspace elapsed cfg helapsed htrace i).trans (Nat.le_max_left _ _)⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun
