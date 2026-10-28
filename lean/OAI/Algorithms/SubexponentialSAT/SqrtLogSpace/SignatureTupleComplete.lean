import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleCommand
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleBranchSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureKeySource

/-! Concrete cursor invariants for the fixed attained-signature controller.
The integer head matrices come from native source words.  Each boundary uses
one retained cap; reload and predecessor-scan prefix bounds remain transient.
-/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete

open Classical
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource

theorem cursor_enabled (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ)
    (cursor : Cursor key levels) (a : State 40 896)
    (ha : CursorStorage h key levels base cursor a)
    (hactive : a.regs controllerPorts.active=true) :
    ∃ event after, Step key levels event cursor after := by
  classical
  cases ha with
  | @scan depth ancestors candidate a hs =>
    by_cases hc : candidate < 2 ^ h depth.val
    · let c : Fin (2^h depth.val) := ⟨candidate,hc⟩
      by_cases hf : ∀ j, j < c → key depth.val j ≠ key depth.val c
      · exact ⟨_,_,Step.fresh depth ancestors ⟨c,hf⟩⟩
      · exact ⟨_,_,Step.duplicate depth ancestors c hf⟩
    · have he : candidate=2^h depth.val := by have hb := hs.range; omega
      subst candidate
      exact ⟨_,_,Step.exhausted depth ancestors⟩
  | leaf hs => exact ⟨_,_,Step.leaf _⟩
  | halt hf => simp only [hf,Bool.false_eq_true] at hactive


open BucketTupleProgram.Concrete LayoutProgram OAI.Algorithms.SubexponentialSAT.MulticolorTypes OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking in
/-- The numeric attained cursor denotes the original free-head assignment;
all integer matrix rows remain in the key. -/
theorem ordered_integerKey {r Q d n : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (head : Fin Q → Fin n → Fin r)
    (H : Finset (Fin n)) (node : Fin Q) (g : Fin r)
    (js : List ℕ) (hb : ∀ v ∈ js, v < n) (hn : js.Nodup)
    (hs : ∀ v : Fin n,v.val∈js ↔ ∃ _ : v∉H,head node v=g)
    (candidate : Fin (2^js.length)) :
    AttainedSignatures.integerKey
      (fun (j : Fin ps.length) (i : Fin js.length) =>
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R node j.val (js.get i)) candidate =
      HeadSourceLocality.freeLabel p ps P owner head H node g
        ((freeAssignmentEquiv H (fun v => head node v.val) g js hb hn hs).symm
          (AttainedSignatures.assignmentEquiv js.length candidate)) := by
  simpa only [AttainedSignatures.integerKey,Equiv.apply_symm_apply] using
    SignatureKeySource.ordered_signature p ps P owner head H node g js hb hn hs
      ((freeAssignmentEquiv H (fun v => head node v.val) g js hb hn hs).symm
        (AttainedSignatures.assignmentEquiv js.length candidate))


/-- Persistent query words are disjoint from the loader scratch, current
head descriptors and tuple controller. This includes all ring caches, masks,
formula words and the pair accumulator; low649 is tracked separately. -/
structure PersistentPort (i : Fin 896) : Prop where
  outsideWork : (i.val < 340) ∨ (628 ≤ i.val)
  head : i∉([649,650,651,652,659,668,669,670,671] : List (Fin 896))
  tuple : ∀ j : Fin 12,i≠tupleStacks j

theorem PersistentPort.not_fresh {i : Fin 896} (h : PersistentPort i) : i≠rescanStacks 22 := by
  intro he
  have hp := h.outsideWork
  have hv := congrArg Fin.val he
  change i.val=362 at hv
  rcases hp with hp|hp <;> omega

theorem PersistentPort.not_current {i : Fin 896} (h : PersistentPort i) : i∉currentHeadPorts := by
  simp only [currentHeadPorts,List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨h.tuple 2,h.tuple 3,h.tuple 4,h.tuple 5,h.tuple 7,h.tuple 8,h.tuple 10,h.tuple 11⟩

/-- The concrete loader retains every persistent query word, including the
finite-ring caches that are not part of its own eighteen input masters. -/
theorem result_persistent (s : Native.Inputs) (z : ℕ) (a : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 896) (hi : PersistentPort i) :
    (result s z a rp rm rs raw shifted).stacks i=a.stacks i := by
  by_cases hlow : i.val < 768
  · let j : Fin 768 := ⟨i.val,hlow⟩
    have he : i=SignatureHeadLoader.lowStacks j := Fin.ext rfl
    have hne (q : Fin 768)
        (hm : SignatureHeadLoader.lowStacks q∈([649,650,651,652,659,668,669,670,671] : List (Fin 896))) :
        j≠q := by
      intro hj
      apply hi.head
      simpa only [he,hj] using hm
    have hj : Protected j := ⟨hi.outsideWork,hne 659 (by decide)⟩
    rw [he,result_low s z a rp rm rs raw shifted j
      (hne 659 (by decide)) (hne 668 (by decide))
      (hne 669 (by decide))]
    rw [SignatureHeadLoader.localResult_frame _ _ _ _ _ _ _ _ _ _ _ _ j hj
      (hne 650 (by decide)) (hne 651 (by decide))
      (hne 652 (by decide)) (hne 668 (by decide))
      (hne 669 (by decide)) (hne 670 (by decide))
      (hne 671 (by decide))]
    have ha : i∉([649,659,846,847] : List (Fin 896)) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨fun h => hi.head (by simp [h]),fun h => hi.head (by simp [h]),hi.tuple 10,hi.tuple 11⟩
    rw [he] at ha
    exact SignatureHeadLoader.addressStateFrom_frame 845 _ (SignatureHeadLoader.lowStacks j) ha
  · apply result_high_frame
    · omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨hi.tuple 10,hi.tuple 11⟩

theorem reset_persistent (a : State 40 896) (i : Fin 896) (hi : PersistentPort i) :
    (resetGeneratorState a).stacks i=a.stacks i :=
  resetGeneratorState_outside a i (hi.tuple 2) (hi.tuple 4) (hi.tuple 7) (hi.tuple 8)

theorem resume_persistent (a : State 40 896) (h c : ℕ) (hw : CursorWords a h c)
    (i : Fin 896) (hi : PersistentPort i) :
    (advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) a)).stacks i=a.stacks i := by
  have hc := copyPredecessor_cursor a h c hw
  rw [advanceCandidateState_outside _ hc.incrementScratch i
    (hi.tuple 3) (hi.tuple 2) (hi.tuple 7) (hi.tuple 5)]
  simp only [SignatureTupleProgram.copyState,StackRoutines.copyStacks,Function.update_of_ne (hi.tuple 8)]


/-- The concrete raw/shifted matrix is retained as proof evidence only.
Runtime storage is the encoded shifted matrix on847 and bounded cursors. -/
structure ScanMatrix (s : ProducedSource) (depth candidate : ℕ) (a : State 40 896) : Prop where
  data : ∃ raw shifted,
    LayoutMatrixProgram.MatrixRel s.input.relation s.input.columnLength s.input.D
      (selectedHeads s.input.n s.input.rows s.input.low (s.base+depth)) raw ∧
    List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (s.source.stacks 141))) raw shifted ∧
    ∀ hc : candidate < 2 ^ s.headSize depth,
      CandidateReady a (s.source.stacks 141) shifted (s.headSize depth) ⟨candidate,hc⟩

/-- Low649 is explicit: it is reused as the node base at the next pair.
The current physical address is maintained across every scan boundary. -/
structure ScanBoundary (s : ProducedSource) (F : ℕ) (depth : Fin s.input.r)
    (ancestors : Prefix (Representatives s.key) depth.val) (candidate : ℕ)
    (a : State 40 896) : Prop extends
    ScanStorage s.headSize s.key s.input.r s.base depth ancestors candidate a where
  bound : WordBound F a
  masters : SignatureHeadLoader.MasterFrame s.masters
    (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)
  matrix : ScanMatrix s depth.val candidate a
  address649 : a.stacks 649=unary (s.base+depth.val)

structure LeafBoundary (s : ProducedSource) (F : ℕ)
    (ancestors : Prefix (Representatives s.key) s.input.r) (a : State 40 896) : Prop extends
    LeafStorage s.headSize s.key s.input.r s.base ancestors a where
  bound : WordBound F a
  masters : SignatureHeadLoader.MasterFrame s.masters
    (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)
  zero_address649 : s.input.r=0 → a.stacks 649=unary s.base

structure HaltBoundary (s : ProducedSource) (F : ℕ) (a : State 40 896) : Prop where
  active : a.regs controllerPorts.active=false
  bound : WordBound F a
  masters : SignatureHeadLoader.MasterFrame s.masters
    (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)
  address649 : a.stacks 649=unary s.base

inductive Boundary (s : ProducedSource) (F : ℕ) : Cursor s.key s.input.r → State 40 896 → Prop
  | scan {depth ancestors candidate a} : ScanBoundary s F depth ancestors candidate a →
      Boundary s F (.scan depth ancestors candidate) a
  | leaf {ancestors a} : LeafBoundary s F ancestors a → Boundary s F (.leaf ancestors) a
  | halt {a} : HaltBoundary s F a → Boundary s F .halt a

theorem Boundary.cursorStorage {s : ProducedSource} {F : ℕ}
    {cursor : Cursor s.key s.input.r} {a : State 40 896}
    (ha : Boundary s F cursor a) :
    CursorStorage s.headSize s.key s.input.r s.base cursor a := by
  cases ha with
  | scan hs => exact .scan hs.toScanStorage
  | leaf hs => exact .leaf hs.toLeafStorage
  | halt hs => exact .halt hs.active

theorem Boundary.wordBound {s : ProducedSource} {F : ℕ}
    {cursor : Cursor s.key s.input.r} {a : State 40 896}
    (ha : Boundary s F cursor a) : WordBound F a := by
  cases ha with
  | scan hs => exact hs.bound
  | leaf hs => exact hs.bound
  | halt hs => exact hs.bound

/-- Static bounds are chosen once before traversal; they are never updated
with a transient prefix bound or with a candidate's numeric value. -/
structure RetainedCap (s : ProducedSource) (F : ℕ) : Prop where
  positive : 1 ≤ F
  cursor : s.input.n+1 ≤ F
  frames : 6*s.input.r*(s.input.n+1)+(s.base+s.input.r)+(s.input.n+1) ≤ F
  output : SignatureHeadLoader.retainedOutputBound s.input.n s.input.N s.input.D
    s.input.columnLength s.bound ≤ F
  scanner : scannerEnvelope s.bound ≤ F

private theorem master_not_candidate (i : Fin 768) : SignatureHeadLoader.lowStacks i≠candidatePorts.counter := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=838 at hv
  omega

private theorem master_not_remaining (i : Fin 768) : SignatureHeadLoader.lowStacks i≠remainingPorts.counter := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=843 at hv
  omega

private theorem master_not_fresh (i : Fin 768) (hi : i∈SignatureHeadLoader.masters) :
    SignatureHeadLoader.lowStacks i≠rescanStacks 22 := by
  simp only [SignatureHeadLoader.masters,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- Losing-candidate scans preserve the actual source and native caches. -/
theorem duplicate_masters (s : ProducedSource) (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ) (candidate : Fin (2^h))
    (ready : CandidateReady a W rows h candidate) (hw : CursorWords a h candidate.val)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (advanceCandidateState (probePostState a out W rows h candidate))) := by
  constructor
  intro i hi
  exact (duplicate_stack_frame a out W rows h candidate ready hw _
    (master_not_candidate i) (master_not_remaining i) (master_not_fresh i hi)).trans (hm.stored i hi)

/-- Every probe compares exactly the literal full integer signature of this
head; the finite-key model has no invented coordinate tuples. -/
theorem scan_kernel (s : ProducedSource) (depth : ℕ)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel s.input.relation s.input.columnLength s.input.D
      (selectedHeads s.input.n s.input.rows s.input.low (s.base+depth)) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord (s.source.stacks 141))) raw shifted)
    (i j : Fin (2^s.headSize depth)) :
    AttainedSignatureProgram.Rescan.naturalKey (s.source.stacks 141) shifted (s.headSize depth) i=
      AttainedSignatureProgram.Rescan.naturalKey (s.source.stacks 141) shifted (s.headSize depth) j ↔
      s.key depth i=s.key depth j :=
  shifted_key_kernel s.input (s.source.stacks 141) s.offset_value s.owner s.plans
    s.plans_eq s.owners_eq (s.base+depth) raw shifted hr hy i j

/-- Fixed time and prefix caps for one controller event. Candidate numbers
occur only as a multiplicative running-time charge. -/
def eventPolynomial (s : ProducedSource) (F : ℕ) : ℕ :=
  scannerEnvelope s.bound+runEnvelope s.bound F+200*F+200

def prefixEnvelope (s : ProducedSource) (F : ℕ) : ℕ :=
  4000*(F+1)+runEnvelope s.bound F

private theorem probe_advance_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val) (candidate : Fin (2^h depth.val))
    (a : State 40 896) (out : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool)))
    (ha : ScanStorage h key levels base depth ancestors candidate.val a)
    (ready : CandidateReady a W rows (h depth.val) candidate) :
    ScanStorage h key levels base depth ancestors (candidate.val+1)
      (advanceCandidateState (probePostState a out W rows (h depth.val) candidate)) := by
  let b := probePostState a out W rows (h depth.val) candidate
  have hw := SignatureRescanBridge.probe_preserves_cursor a out W rows (h depth.val) candidate
    ready ha.toCursorWords
  have hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter)=false := by
    rw [ha.toCursorWords.available]
    simp only [Nat.ne_of_lt candidate.isLt,decide_false]
  have hf := SignatureRescanBridge.probe_control_flags a out W rows (h depth.val) candidate hzero
  have frame (i : Fin 896) (hk : i≠rescanStacks 17) (hl : i≠rescanStacks 22) : b.stacks i=a.stacks i :=
    SignatureRescanBridge.probe_stack_frame a out W rows (h depth.val) candidate ready
      ha.decrementScratch i hk hl
  have hb : AncestorStorage h key levels base depth.val ancestors b := by
    refine ⟨ha.depth_le,?_,?_,?_,?_,hf.1.trans ha.active⟩
    · exact (frame _ (by decide) (by decide)).trans ha.cursors
    · exact (frame _ (by decide) (by decide)).trans ha.representatives
    · exact (frame _ (by decide) (by decide)).trans ha.heads
    · exact (frame _ (by decide) (by decide)).trans ha.address
  exact advance_scan_storage h key levels base depth ancestors candidate.val b hb hw candidate.isLt
    (hf.2.1.trans ha.leaf) ((frame _ (by decide) (by decide)).trans ha.payload)
    ((frame _ (by decide) (by decide)).trans ha.predecessor)

/-- The complete losing-candidate event uses the actual full-key scanner.
The returned iteration, semantic cursor, fixed retained cap and all-prefix
storage refer to one and the same execution. -/
theorem duplicate_step (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (visit : Cmd 40 896) (depth : Fin s.input.r)
    (ancestors : Prefix (Representatives s.key) depth.val)
    (candidate : Fin (2^s.headSize depth.val)) (a : State 40 896)
    (ha : ScanBoundary s F depth ancestors candidate.val a)
    (hdup : ¬ ∀ j, j < candidate → s.key depth.val j ≠ s.key depth.val candidate) :
    ∃ n b, Iteration controllerPorts (assembleRoutines loadHead candidateCall visit) n a b ∧
      ScanBoundary s F depth ancestors (candidate.val+1) b ∧
      n+1 ≤ (candidate.val+1)*eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (body controllerPorts
        (assembleRoutines loadHead candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧
      ∀ i : Fin 896,i≠838 → i≠843 → i≠362 → b.stacks i=a.stacks i := by
  obtain ⟨raw,shifted,hr,hy,hready⟩ := ha.matrix.data
  have ready := hready candidate.isLt
  let C := 3*(s.input.columnLength+s.bound)+1
  have hshape := shifted_rows_bounds s.input (s.base+depth.val) s.bound
    (s.source.stacks 141) raw shifted (s.bounded 141) hr hy
  have hbud := scanner_caps_polynomial s.input s.source s.bound (s.base+depth.val)
    s.ready s.bounded (s.source.stacks 141) (s.bounded 141) raw shifted hr hy
  have hkernel := scan_kernel s depth.val raw shifted hr hy
  have hactual := (actual_duplicate_iff_model _ _ hkernel candidate).mpr hdup
  obtain ⟨n,out,he,hbound,hprefix,ht⟩ := duplicate_run_space loadHead visit a
    (s.source.stacks 141) shifted (s.headSize depth.val) C F candidate ready
    ha.toCursorWords hshape.2.1 hshape.2.2 ha.leaf hactual ha.bound cap.positive
    ((Nat.add_le_add_right (s.headSize_le depth.val) 1).trans cap.cursor)
    (hbud.2.2.trans cap.scanner) (hbud.2.1.trans cap.scanner)
  let b := advanceCandidateState (probePostState a out (s.source.stacks 141) shifted
    (s.headSize depth.val) candidate)
  have hb : ScanBoundary s F depth ancestors (candidate.val+1) b := by
    refine ⟨probe_advance_storage s.headSize s.key s.input.r s.base depth ancestors candidate a out
      (s.source.stacks 141) shifted ha.toScanStorage ready,hbound,
      duplicate_masters s a out (s.source.stacks 141) shifted (s.headSize depth.val)
        candidate ready ha.toCursorWords ha.masters,?_,?_⟩
    · constructor
      refine ⟨raw,shifted,hr,hy,?_⟩
      intro hc
      exact probe_advance_ready a out (s.source.stacks 141) shifted (s.headSize depth.val)
        candidate ⟨candidate.val+1,hc⟩ rfl ready ha.toCursorWords
    · exact (duplicate_stack_frame a out (s.source.stacks 141) shifted (s.headSize depth.val)
        candidate ready ha.toCursorWords 649 (by decide) (by decide) (by decide)).trans ha.address649
  refine ⟨n,b,SignatureTupleBranchSpace.iteration_of_eval he,hb,?_,?_,?_⟩
  · apply ht.trans
    apply Nat.mul_le_mul_left
    have hp : AttainedSignatureProgram.Rescan.polynomialBudget (s.source.stacks 141)
        shifted (s.headSize depth.val) C ≤ scannerEnvelope s.bound := hbud.1
    unfold eventPolynomial
    omega
  · intro p q hp hq i
    exact (hprefix p q hp hq i).trans (by unfold prefixEnvelope; omega)
  · intro i hc hr hf
    exact duplicate_stack_frame a out (s.source.stacks 141) shifted (s.headSize depth.val)
      candidate ready ha.toCursorWords i hc hr hf

private theorem low_not_tuple (i : Fin 768) (j : Fin 12) :
    SignatureHeadLoader.lowStacks i≠tupleStacks j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=836+j.val at hv
  omega

theorem reset_masters (s : ProducedSource) (a : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks (resetGeneratorState a)) := by
  constructor
  intro i hi
  exact (resetGeneratorState_outside a (SignatureHeadLoader.lowStacks i)
    (low_not_tuple i 2) (low_not_tuple i 4) (low_not_tuple i 7) (low_not_tuple i 8)).trans
    (hm.stored i hi)

private theorem probe_ancestors (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (candidate : Fin (2^h depth))
    (a : State 40 896) (out : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool)))
    (ha : AncestorStorage h key levels base depth ancestors a)
    (hw : CursorWords a (h depth) candidate.val)
    (ready : CandidateReady a W rows (h depth) candidate) :
    AncestorStorage h key levels base depth ancestors
      (probePostState a out W rows (h depth) candidate) := by
  have frame (i : Fin 896) (hk : i≠rescanStacks 17) (hl : i≠rescanStacks 22) :=
    SignatureRescanBridge.probe_stack_frame a out W rows (h depth) candidate ready
      hw.decrementScratch i hk hl
  refine ⟨ha.depth_le,?_,?_,?_,?_,?_⟩
  · exact (frame _ (by decide) (by decide)).trans ha.cursors
  · exact (frame _ (by decide) (by decide)).trans ha.representatives
  · exact (frame _ (by decide) (by decide)).trans ha.heads
  · exact (frame _ (by decide) (by decide)).trans ha.address
  · exact (SignatureRescanBridge.probe_register_frame a out W rows (h depth) candidate
      controllerPorts.active (by decide) (by decide) (by decide)).trans ha.active

theorem candidate_descent_cost (candidate P S R F np nd fuel latch : ℕ)
    (hp : P ≤ S) (hf : fuel ≤ F) (hl : latch ≤ F)
    (hprobe : np ≤ (candidate+1)*P+8*fuel+2*latch+16)
    (hdesc : nd+1 ≤ R+100*F+100) :
    np+nd+3+1 ≤ (candidate+1)*(S+R+200*F+200) := by
  have hpc := Nat.mul_le_mul_left (candidate+1) hp
  have hm : R+200*F+200 ≤ (candidate+1)*(R+200*F+200) := by
    simpa only [one_mul] using Nat.mul_le_mul_right (R+200*F+200)
      (show 1 ≤ candidate+1 by omega)
  calc
    _ ≤ (candidate+1)*S+(R+200*F+200) := by omega
    _ ≤ (candidate+1)*S+(candidate+1)*(R+200*F+200) := Nat.add_le_add_left hm _
    _=(candidate+1)*(S+R+200*F+200) := by ring


/-- A fresh nonfinal head runs the actual predicate and native child reload,
then starts that child's bounded zero cursor. The retained path contains only
first occurrences, never the raw Cartesian product of head assignments. -/
theorem fresh_internal_step (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (visit : Cmd 40 896) (depth : Fin s.input.r)
    (ancestors : Prefix (Representatives s.key) depth.val)
    (rep : Representatives s.key depth.val) (a : State 40 896)
    (ha : ScanBoundary s F depth ancestors rep.val.val a) (hd : depth.val + 1 < s.input.r) :
    ∃ n b, Iteration controllerPorts (assembleRoutines loadHead candidateCall visit) n a b ∧
      ScanBoundary s F ⟨depth.val+1,hd⟩ (Fin.snoc ancestors rep) 0 b ∧
      n+1 ≤ (rep.val.val+1)*eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (body controllerPorts
        (assembleRoutines loadHead candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧ ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  obtain ⟨raw,shifted,hr,hy,hready⟩ := ha.matrix.data
  have ready := hready rep.val.isLt
  let C := 3*(s.input.columnLength+s.bound)+1
  have hshape := shifted_rows_bounds s.input (s.base+depth.val) s.bound
    (s.source.stacks 141) raw shifted (s.bounded 141) hr hy
  have hbud := scanner_caps_polynomial s.input s.source s.bound (s.base+depth.val)
    s.ready s.bounded (s.source.stacks 141) (s.bounded 141) raw shifted hr hy
  have hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter)=false := by
    rw [ha.toCursorWords.available]
    simp only [Nat.ne_of_lt rep.val.isLt,decide_false]
  obtain ⟨np,hnp,out,hprobe,hprobeSpace⟩ := SignatureRescanBridge.probe_run_space a
    (s.source.stacks 141) shifted (s.headSize depth.val) C F hshape.2.1 hshape.2.2
    rep.val ready ha.decrementScratch hzero ha.bound
  let b := probePostState a out (s.source.stacks 141) shifted (s.headSize depth.val) rep.val
  have hb := probe_endpoint_bound a out (s.source.stacks 141) shifted (s.headSize depth.val)
    C F rep.val ready ha.decrementScratch hshape.2.1 hshape.2.2 ha.bound cap.positive
    (hbud.2.2.trans cap.scanner)
  have hcursor := SignatureRescanBridge.probe_preserves_cursor a out (s.source.stacks 141)
    shifted (s.headSize depth.val) rep.val ready ha.toCursorWords
  have hanc := probe_ancestors s.headSize s.key s.input.r s.base depth.val ancestors rep.val
    a out (s.source.stacks 141) shifted ha.toAncestorStorage ha.toCursorWords ready
  have frame (i : Fin 896) (hk : i≠rescanStacks 17) (hl : i≠rescanStacks 22) : b.stacks i=a.stacks i :=
    SignatureRescanBridge.probe_stack_frame a out (s.source.stacks 141) shifted
      (s.headSize depth.val) rep.val ready ha.decrementScratch i hk hl
  have hmasters : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
    constructor
    intro i hi
    exact (frame _ (low_not_tuple i 3) (master_not_fresh i hi)).trans (ha.masters.stored i hi)
  have hW : b.stacks 141=s.source.stacks 141 := (frame 141 (by decide) (by decide)).trans ready.offset
  have hp : b.stacks (tupleStacks 4)=[] := (frame _ (by decide) (by decide)).trans ha.payload
  obtain ⟨rp,rm,rs,childRaw,childShifted,nd,hdesc,hdt,hend,hscan,hchildReady,hraw,hshift,hdescSpace⟩ :=
    descend_native_run s.headSize s.key s.input.r s.base depth.val ancestors rep hd s.input
      s.source s.ready s.bound s.bounded s.rows s.addressRegisters s.dimensionRegisters
      s.cacheRegisters s.cacheWords s.cache b hmasters hanc hcursor hp F s.bound s.input.n hb
      (by simpa only [hW] using s.bounded 141) cap.output (fun d _ => s.headSize_le d) cap.frames rfl
  let finish := resetGeneratorState (result s.input (s.base+(depth.val+1))
    (descendClearState b) rp rm rs childRaw childShifted)
  have hflags := SignatureRescanBridge.probe_control_flags a out (s.source.stacks 141)
    shifted (s.headSize depth.val) rep.val hzero
  have hfresh : b.regs controllerPorts.fresh=true := by
    rw [hflags.2.2.2]
    exact (actual_fresh_iff_model _ _ (scan_kernel s depth.val raw shifted hr hy) rep.val).mpr rep.property
  have hnext : ScanBoundary s F ⟨depth.val+1,hd⟩ (Fin.snoc ancestors rep) 0 finish := by
    refine ⟨hscan,hend,?_,?_,?_⟩
    · apply reset_masters
      apply result_masters
      exact fresh_descent_masters a out (s.source.stacks 141) shifted (s.headSize depth.val)
        rep.val ready ha.decrementScratch s.masters ha.masters
    · constructor
      refine ⟨childRaw,childShifted,hraw,?_,?_⟩
      · simpa only [hW] using hshift
      · intro hc
        simpa only [hW] using hchildReady
    · rw [reset_result_address649]
      exact (descend_ancestor_storage s.headSize s.key s.input.r s.base depth.val ancestors rep b
        depth.isLt hanc hcursor hp).address
  have hit : Iteration controllerPorts (assembleRoutines loadHead candidateCall visit)
      (np+nd+3) a finish := .fresh ha.leaf hprobe hflags.2.2.1 hfresh hdesc
  refine ⟨_,finish,hit,hnext,?_,?_,?_⟩
  · exact candidate_descent_cost rep.val.val _ _ _ F np nd _ _ hbud.1
      (ha.bound remainingPorts.counter) (ha.bound (rescanStacks 22)) hnp hdt
  · apply fresh_body_prefix_bound loadHead visit a b finish np nd (prefixEnvelope s F)
      ha.leaf hflags.2.2.1 hfresh hprobe hdesc
    · intro p q hp hq i
      have hs : AttainedSignatureProgram.Rescan.spaceBudget (s.source.stacks 141)
          shifted (s.headSize depth.val) C ≤ F := hbud.2.1.trans cap.scanner
      have hcounter := ha.bound remainingPorts.counter
      have hlatch := ha.bound (rescanStacks 22)
      exact (hprobeSpace p q (by omega) hq i).trans (by unfold prefixEnvelope; omega)
    · intro p q hp hq i
      exact (hdescSpace p q (by omega) hq i).trans (by unfold prefixEnvelope; omega)

  · intro i hi
    rw [reset_persistent _ i hi,result_persistent _ _ _ _ _ _ _ _ i hi]
    exact fresh_descent_stack_frame a out (s.source.stacks 141) shifted (s.headSize depth.val)
      rep.val ready ha.decrementScratch i hi.tuple hi.not_fresh

theorem final_descend_cursor (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val) (rep : Representatives key depth.val)
    (a : State 40 896) (ha : AncestorStorage h key levels base depth.val ancestors a)
    (hw : CursorWords a (h depth.val) rep.val.val) (hp : a.stacks (tupleStacks 4)=[])
    (hlast : depth.val+1=levels) :
    CursorStorage h key levels base
      (enter key levels (depth.val+1) depth.isLt (Fin.snoc ancestors rep)) (descendClearState a) := by
  cases levels with
  | zero => exact Fin.elim0 depth
  | succ m =>
    have he : depth=Fin.last m := Fin.ext (by simpa only [Fin.val_last] using Nat.add_right_cancel hlast)
    subst depth
    simpa only [Fin.val_last,enter_leaf] using
      (CursorStorage.leaf (descend_leaf_storage h key m base ancestors rep a ha hw hp))


/-- The last attained head reaches the actual cleaned tuple visitor state.
There is one such state per attained full tuple, including empty head words. -/
theorem fresh_final_step (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (visit : Cmd 40 896) (depth : Fin s.input.r)
    (ancestors : Prefix (Representatives s.key) depth.val)
    (rep : Representatives s.key depth.val) (a : State 40 896)
    (ha : ScanBoundary s F depth ancestors rep.val.val a) (hlast : depth.val+1=s.input.r) :
    ∃ n b, Iteration controllerPorts (assembleRoutines loadHead candidateCall visit) n a b ∧
      Boundary s F (enter s.key s.input.r (depth.val+1) depth.isLt (Fin.snoc ancestors rep)) b ∧
      n+1 ≤ (rep.val.val+1)*eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (body controllerPorts
        (assembleRoutines loadHead candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧ ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  obtain ⟨raw,shifted,hr,hy,hready⟩ := ha.matrix.data
  have ready := hready rep.val.isLt
  let C := 3*(s.input.columnLength+s.bound)+1
  have hshape := shifted_rows_bounds s.input (s.base+depth.val) s.bound
    (s.source.stacks 141) raw shifted (s.bounded 141) hr hy
  have hbud := scanner_caps_polynomial s.input s.source s.bound (s.base+depth.val)
    s.ready s.bounded (s.source.stacks 141) (s.bounded 141) raw shifted hr hy
  have hactual := (actual_fresh_iff_model _ _ (scan_kernel s depth.val raw shifted hr hy) rep.val).mpr
    rep.property
  have hheads : a.stacks (tupleStacks 6)=[true] := by
    rw [ha.heads]
    have he : s.input.r-depth.val=1 := by omega
    rw [he]
    rfl
  obtain ⟨n,out,he,hprefix,ht⟩ := fresh_leaf_run_space loadHead visit a (s.source.stacks 141)
    shifted (s.headSize depth.val) C F (s.base+depth.val) rep.val ready ha.toCursorWords
    hshape.2.1 hshape.2.2 ha.leaf hactual ha.payload hheads ha.address ha.bound cap.positive
    ((Nat.add_le_add_right (s.headSize_le depth.val) 1).trans cap.cursor)
    (hbud.2.2.trans cap.scanner) (hbud.2.1.trans cap.scanner)
  let b := probePostState a out (s.source.stacks 141) shifted (s.headSize depth.val) rep.val
  have hb := probe_endpoint_bound a out (s.source.stacks 141) shifted (s.headSize depth.val)
    C F rep.val ready ha.decrementScratch hshape.2.1 hshape.2.2 ha.bound cap.positive
    (hbud.2.2.trans cap.scanner)
  have hcursor := SignatureRescanBridge.probe_preserves_cursor a out (s.source.stacks 141)
    shifted (s.headSize depth.val) rep.val ready ha.toCursorWords
  have hanc := probe_ancestors s.headSize s.key s.input.r s.base depth.val ancestors rep.val
    a out (s.source.stacks 141) shifted ha.toAncestorStorage ha.toCursorWords ready
  have hp : b.stacks (tupleStacks 4)=[] :=
    (SignatureRescanBridge.probe_stack_frame a out (s.source.stacks 141) shifted
      (s.headSize depth.val) rep.val ready ha.decrementScratch _ (by decide) (by decide)).trans ha.payload
  have hstorage := final_descend_cursor s.headSize s.key s.input.r s.base depth ancestors rep b
    hanc hcursor hp hlast
  have hend := descend_endpoint_bound s.headSize s.key s.input.r s.base depth.val s.input.n F
    ancestors rep b depth.isLt hanc hcursor hp (fun d _ => s.headSize_le d) (by have := cap.frames; omega) hb
  have hmasters := fresh_descent_masters a out (s.source.stacks 141) shifted (s.headSize depth.val)
    rep.val ready ha.decrementScratch s.masters ha.masters
  have hnext : Boundary s F
      (enter s.key s.input.r (depth.val+1) depth.isLt (Fin.snoc ancestors rep)) (descendClearState b) := by
    rw [enter,dite_eq_left hlast] at hstorage ⊢
    cases hstorage with
    | leaf hl =>
      apply Boundary.leaf
      refine ⟨hl,hend,hmasters,?_⟩
      intro hz
      have hp := depth.isLt
      omega
  refine ⟨n,descendClearState b,SignatureTupleBranchSpace.iteration_of_eval he,hnext,?_,?_,?_⟩
  · apply ht.trans
    apply Nat.mul_le_mul_left
    have hp : AttainedSignatureProgram.Rescan.polynomialBudget (s.source.stacks 141)
        shifted (s.headSize depth.val) C ≤ scannerEnvelope s.bound := hbud.1
    unfold eventPolynomial
    omega
  · intro p q hp hq i
    exact (hprefix p q hp hq i).trans (by unfold prefixEnvelope; omega)

  · intro i hi
    exact fresh_descent_stack_frame a out (s.source.stacks 141) shifted (s.headSize depth.val)
      rep.val ready ha.decrementScratch i hi.tuple hi.not_fresh

private theorem resume_masters (s : ProducedSource) (a : State 40 896) (h c : ℕ)
    (hw : CursorWords a h c)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) a))) := by
  constructor
  intro i hi
  have hc := copyPredecessor_cursor a h c hw
  change (advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) a)).stacks
    (SignatureHeadLoader.lowStacks i)=_
  rw [advanceCandidateState_outside _ hc.incrementScratch _
    (low_not_tuple i 3) (low_not_tuple i 2) (low_not_tuple i 7) (low_not_tuple i 5)]
  simp only [SignatureTupleProgram.copyState,StackRoutines.copyStacks,Function.update_of_ne (low_not_tuple i 8)]
  exact hm.stored i hi

/-- A nonroot return restores its attained parent, reconstructs only that
parent's matrix and advances its saved cursor once. -/
theorem ascend_parent (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (depth : Fin s.input.r) (ancestors : Prefix (Representatives s.key) (depth.val+1))
    (a : State 40 896)
    (ha : AncestorStorage s.headSize s.key s.input.r s.base (depth.val+1) ancestors a)
    (hb : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    ∃ n b, Eval (ascendWith loadHead) n a b ∧
      ScanBoundary s F depth (Fin.init ancestors)
        ((ancestors (Fin.last depth.val)).val.val+1) b ∧
      n+1 ≤ runEnvelope s.bound F+69*F+100 ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (ascendWith loadHead) 0 0) p
        (a.withPC (some (compiled (ascendWith loadHead) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧ ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  have hW := s.source_offset a hm
  obtain ⟨rp,rm,rs,raw,shifted,n,he,ht,hbound,hscan,hready,hraw,hshift,hprefix⟩ :=
    ascend_native_run s.headSize s.key s.input.r s.base depth ancestors s.input s.source
      s.ready s.bound s.bounded s.rows s.addressRegisters s.dimensionRegisters s.cacheRegisters
      s.cacheWords s.cache a hm ha F s.bound s.input.n hb
      (by simpa only [hW] using s.bounded 141) cap.output (fun d _ => s.headSize_le d) cap.frames rfl
  let parent := parentReturnState s.headSize s.key depth.val ancestors a
  let loaded := result s.input (s.base+depth.val) parent rp rm rs raw shifted
  let finish := advanceCandidateState (SignatureTupleProgram.copyState 651 (tupleStacks 8) loaded)
  have hw := result_cursor_words s.input (s.base+depth.val) parent rp rm rs raw shifted _ _
    (parent_return_cursor s.headSize s.key depth.val ancestors a)
  have hloadedMasters : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks loaded) :=
    result_masters s.input (s.base+depth.val) parent rp rm rs raw shifted s.masters
      (parent_return_masters s.headSize s.key depth.val ancestors a s.masters hm)
  have hnext : ScanBoundary s F depth (Fin.init ancestors)
      ((ancestors (Fin.last depth.val)).val.val+1) finish := by
    refine ⟨hscan,hbound,resume_masters s loaded _ _ hw hloadedMasters,?_,?_⟩
    · constructor
      refine ⟨raw,shifted,hraw,?_,?_⟩
      · simpa only [hW] using hshift
      · intro hc
        simpa only [hW] using hready hc
    · rw [resume_loaded_address649 loaded _ _ hw,result_address649]
      exact (parent_return_ancestor_storage s.headSize s.key s.input.r s.base depth.val ancestors a ha).address
  refine ⟨n,finish,he,hnext,ht,?_,?_⟩
  · intro p q hp hq i
    exact (hprefix p q hp hq i).trans (by unfold prefixEnvelope; omega)

  · intro i hi
    rw [resume_persistent loaded _ _ hw i hi,result_persistent _ _ _ _ _ _ _ _ i hi]
    exact parentReturnState_outside_tuple s.headSize s.key depth.val ancestors a i hi.tuple

private theorem low_not_current (i : Fin 768) : SignatureHeadLoader.lowStacks i∉currentHeadPorts := by
  simp only [currentHeadPorts,List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨low_not_tuple i 2,low_not_tuple i 3,low_not_tuple i 4,low_not_tuple i 5,
    low_not_tuple i 7,low_not_tuple i 8,low_not_tuple i 10,low_not_tuple i 11⟩

/-- Exhausting the root returns low649 unchanged, so another finite-
difference pair starts at the same node base. -/
theorem exhausted_root_step (s : ProducedSource) (F : ℕ) (visit : Cmd 40 896)
    (depth : Fin s.input.r) (ancestors : Prefix (Representatives s.key) depth.val)
    (a : State 40 896) (ha : ScanBoundary s F depth ancestors (2^s.headSize depth.val) a)
    (hd : depth.val=0) :
    ∃ n b, Iteration controllerPorts (assembleRoutines loadHead candidateCall visit) n a b ∧
      HaltBoundary s F b ∧ n+1 ≤ eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (body controllerPorts
        (assembleRoutines loadHead candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧ ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  have hframes : a.stacks (tupleStacks 0)=[] := by
    rw [ha.cursors]
    simp only [cursorFrames,hd,List.ofFn_zero,List.reverse_nil,List.flatten_nil]
  have hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter)=true := by
    rw [ha.toCursorWords.available]
    simp
  obtain ⟨n,he,halt,hbound,hprefix,ht⟩ := exhausted_root_run_space loadHead visit a F
    ha.leaf hframes ha.decrementScratch hzero ha.bound
  have hb : HaltBoundary s F (rootAscendState (testAvailableState a)) := by
    refine ⟨halt,hbound,?_,?_⟩
    · constructor
      intro i hi
      change (rootAscendState (testAvailableState a)).stacks (SignatureHeadLoader.lowStacks i)=_
      rw [checkedReturnState_stack,ite_eq_right (low_not_current i),testAvailableState_stacks a ha.decrementScratch]
      exact ha.masters.stored i hi
    · rw [exhausted_root_address649 a ha.decrementScratch,ha.address649,hd,Nat.add_zero]
  refine ⟨n,_,SignatureTupleBranchSpace.iteration_of_eval he,hb,?_,?_,?_⟩
  · unfold eventPolynomial
    omega
  · intro p q hp hq i
    exact (hprefix p q hp hq i).trans (by unfold prefixEnvelope; omega)

  · intro i hi
    rw [checkedReturnState_stack,ite_eq_right hi.not_current,testAvailableState_stacks a ha.decrementScratch]

/-- An exhausted nonroot generator performs the actual availability test
and paid parent return. It does not call the predecessor scanner. -/
theorem exhausted_successor_step (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (visit : Cmd 40 896) (depth : Fin s.input.r) (hd : depth.val + 1 < s.input.r)
    (ancestors : Prefix (Representatives s.key) (depth.val+1)) (a : State 40 896)
    (ha : ScanBoundary s F ⟨depth.val+1,hd⟩ ancestors (2^s.headSize (depth.val+1)) a) :
    ∃ n b, Iteration controllerPorts (assembleRoutines loadHead candidateCall visit) n a b ∧
      ScanBoundary s F depth (Fin.init ancestors)
        ((ancestors (Fin.last depth.val)).val.val+1) b ∧
      n+1 ≤ eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (body controllerPorts
        (assembleRoutines loadHead candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧ ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  have hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter)=true := by
    rw [ha.toCursorWords.available]
    simp
  let b := testAvailableState a
  have hstacks := testAvailableState_stacks a ha.decrementScratch
  have hb : WordBound F b := by
    intro i
    change ((testAvailableState a).stacks i).length ≤ F
    rw [hstacks]
    exact ha.bound i
  have hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
    constructor
    intro i hi
    exact (congrFun hstacks _).trans (ha.masters.stored i hi)
  have hanc : AncestorStorage s.headSize s.key s.input.r s.base (depth.val+1) ancestors b := by
    refine ⟨ha.depth_le,?_,?_,?_,?_,?_⟩
    · exact (congrFun hstacks _).trans ha.cursors
    · exact (congrFun hstacks _).trans ha.representatives
    · exact (congrFun hstacks _).trans ha.heads
    · exact (congrFun hstacks _).trans ha.address
    · exact (SignatureRescanBridge.test_available_register_frame a controllerPorts.active
        (by decide) (by decide)).trans ha.active
  obtain ⟨na,c,hasc,hnext,hta,hspacea,hframea⟩ := ascend_parent s F cap depth ancestors b hanc hb hm
  have hp := probe_exhausted_eval a ha.decrementScratch hzero
  have hav : b.regs controllerPorts.available=false := by rw [testAvailableState_flag,hzero]; rfl
  have hit : Iteration controllerPorts (assembleRoutines loadHead candidateCall visit)
      ((8*(a.stacks remainingPorts.counter).length+9)+na+2) a c :=
    .exhausted ha.leaf hp hav hasc
  refine ⟨_,c,hit,hnext,?_,?_,?_⟩
  · have hcounter := ha.bound remainingPorts.counter
    unfold eventPolynomial
    omega
  · apply SignatureTupleBranchSpace.exhausted_body_prefix_bound loadHead visit a b c _ na
      (prefixEnvelope s F) ha.leaf hav hp hasc
    · intro p q hpq hq i
      have hcounter := ha.bound remainingPorts.counter
      exact ((SignatureRescanBridge.exhausted_probe_space a F ha.decrementScratch hzero ha.bound).2
        p q (by omega) hq i).trans (by unfold prefixEnvelope; omega)
    · intro p q hpq hq i
      exact hspacea p q (by omega) hq i

  · intro i hi
    exact (hframea i hi).trans (congrFun hstacks i)

theorem leaf_successor_ancestor (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base depth : ℕ)
    (he : depth+1=levels) (ancestors : Prefix (Representatives key) levels)
    (a : State 40 896) (ha : LeafStorage h key levels base ancestors a) :
    AncestorStorage h key levels base (depth+1) (he.symm ▸ ancestors) a := by
  subst levels
  exact ha.toAncestorStorage

theorem leave_successor (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels depth : ℕ)
    (he : depth+1=levels) (ancestors : Prefix (Representatives key) levels) :
    leave key levels levels le_rfl ancestors=
      Cursor.scan ⟨depth,by omega⟩ (Fin.init (he.symm ▸ ancestors))
        (((he.symm ▸ ancestors) (Fin.last depth)).val.val+1) := by
  subst levels
  rfl


theorem root_return_run (loadHead : Cmd 40 896) (a : State 40 896) (F : ℕ)
    (hf : a.stacks (tupleStacks 0)=[]) (hb : ∀ i,(a.stacks i).length ≤ F) :
    Eval (ascendWith loadHead) (clearWordsTime currentHeadPorts a+2) a (rootAscendState a) ∧
      (rootAscendState a).regs controllerPorts.active=false ∧
      (∀ i,((rootAscendState a).stacks i).length ≤ F) ∧
      clearWordsTime currentHeadPorts a+3 ≤ 16*F+27 ∧
      ∀ p z,p ≤ clearWordsTime currentHeadPorts a+3 →
        Trace (compiled (ascendWith loadHead) 0 0) p
          (a.withPC (some (compiled (ascendWith loadHead) 0 0).entry)) z →
        ∀ i,(z.stacks i).length ≤ 2000*(F+1) := by
  have hc := clearWordsTime_le_on currentHeadPorts a F (fun i _ => hb i)
  change clearWordsTime currentHeadPorts a ≤ 8*(2*F+3) at hc
  refine ⟨rootAscend_eval loadHead a hf,rootAscendState_halt a hf,?_,by omega,?_⟩
  · intro i
    rw [checkedReturnState_stack]
    split_ifs
    · exact Nat.zero_le _
    · exact hb i
  · have hs := StructuredSpace.local_stack_bound (compiled (ascendWith loadHead) 0 0)
      (a := a.withPC (some (compiled (ascendWith loadHead) 0 0).entry))
      (steps := 16*F+27) (StreamResources.dataBits_le_mul _ hb)
    intro p z hp hz i
    exact (hs p z (by omega) hz i).trans (by omega)


theorem leave_zero (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels : ℕ)
    (hz : levels=0) (ancestors : Prefix (Representatives key) levels) :
    leave key levels levels le_rfl ancestors=Cursor.halt := by
  subst levels
  rfl

/-- The fixed return command handles both a completed nonempty tuple and
one empty tuple. It reloads a parent only when a retained frame exists. -/
theorem ascend_leaf (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (ancestors : Prefix (Representatives s.key) s.input.r) (a : State 40 896)
    (ha : LeafBoundary s F ancestors a) :
    ∃ steps b, Eval (ascendWith loadHead) steps a b ∧
      Boundary s F (leave s.key s.input.r s.input.r le_rfl ancestors) b ∧
      steps+1 ≤ eventPolynomial s F ∧
      (∀ p z,p ≤ steps+1 → Trace (compiled (ascendWith loadHead) 0 0) p
        (a.withPC (some (compiled (ascendWith loadHead) 0 0).entry)) z →
        ∀ i,(z.stacks i).length ≤ prefixEnvelope s F) ∧
      ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  by_cases hr : s.input.r=0
  · have hf : a.stacks (tupleStacks 0)=[] := by
      rw [ha.cursors]
      simp only [cursorFrames,hr,List.ofFn_zero,List.reverse_nil,List.flatten_nil]
    obtain ⟨he,halt,hb,ht,hspace⟩ := root_return_run loadHead a F hf ha.bound
    have hnext : HaltBoundary s F (rootAscendState a) := by
      refine ⟨halt,hb,?_,?_⟩
      · constructor
        intro i hi
        change (rootAscendState a).stacks (SignatureHeadLoader.lowStacks i)=_
        rw [checkedReturnState_stack,ite_eq_right (low_not_current i)]
        exact ha.masters.stored i hi
      · rw [checkedReturnState_stack,ite_eq_right (show (649 : Fin 896)∉currentHeadPorts by decide)]
        exact ha.zero_address649 hr
    refine ⟨_,rootAscendState a,he,?_,?_,?_,?_⟩
    · rw [leave_zero s.headSize s.key s.input.r hr ancestors]
      exact Boundary.halt hnext
    · unfold eventPolynomial
      omega
    · intro p z hp hz i
      exact (hspace p z hp hz i).trans (by unfold prefixEnvelope; omega)
    · intro i hi
      rw [checkedReturnState_stack,ite_eq_right hi.not_current]
  · let depth : Fin s.input.r := ⟨s.input.r-1,by omega⟩
    have he : depth.val+1=s.input.r := by dsimp [depth]; omega
    let parentAncestors : Prefix (Representatives s.key) (depth.val+1) := he.symm ▸ ancestors
    have hanc := leaf_successor_ancestor s.headSize s.key s.input.r s.base depth.val he
      ancestors a ha.toLeafStorage
    obtain ⟨steps,b,heval,hb,ht,hspace,hframe⟩ :=
      ascend_parent s F cap depth parentAncestors a hanc ha.bound ha.masters
    refine ⟨steps,b,heval,?_,?_,hspace,hframe⟩
    · rw [leave_successor s.headSize s.key s.input.r depth.val he ancestors]
      exact Boundary.scan hb
    · unfold eventPolynomial
      omega

/-- A single cap chosen before traversal pays both persistent frame banks,
all native head arrays and every scanner key. -/
def retainedEnvelope (B A : ℕ) : ℕ :=
  A+scannerEnvelope B+10000*(B+2)^6+6*B*(B+1)+(B*B+B)+(B+1)+1

theorem retainedEnvelope_cap (s : ProducedSource) (A : ℕ) : RetainedCap s (retainedEnvelope s.bound A) := by
  have hi := NodeTime.inputBounds s.input s.source s.ready s.bound s.bounded
  have hn := hi.n
  have hr := hi.r
  have hnode : s.input.node.val ≤ s.bound := by
    simpa only [s.ready.node,unary,List.length_replicate] using s.bounded 307
  have hbase : s.base ≤ s.bound*s.bound := Nat.mul_le_mul hnode hr
  have hframes : 6*s.input.r*(s.input.n+1) ≤ 6*s.bound*(s.bound+1) := by gcongr
  have hout := retained_output_polynomial s.input s.source s.bound s.ready s.bounded
  constructor <;> unfold retainedEnvelope <;> omega

/-- The retained cap has fixed degree36. No input-dependent exponent is
introduced by the depth, assignment counter or repeated head reconstruction. -/
theorem retainedEnvelope_polynomial (B A : ℕ) :
    retainedEnvelope B A ≤ (100000*20000^6+10050)*(A+B+2)^36 := by
  let X := A+B+2
  change retainedEnvelope B A ≤ (100000*20000^6+10050)*X^36
  have hX : 1 ≤ X := by dsimp [X]; omega
  have h1 : X ≤ X^36 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by decide : 1 ≤ 36)
  have h2 : X^2 ≤ X^36 := pow_le_pow_right₀ hX (by decide)
  have h6 : X^6 ≤ X^36 := pow_le_pow_right₀ hX (by decide)
  have h0 : 1 ≤ X^36 := one_le_pow₀ hX
  have hb : B ≤ X := by dsimp [X]; omega
  have hb1 : B+1 ≤ X := by dsimp [X]; omega
  have hb2 : B+2 ≤ X := by dsimp [X]; omega
  have ha : A ≤ X := by dsimp [X]; omega
  have hscan : scannerEnvelope B ≤ (100000*20000^6)*X^36 := by
    unfold scannerEnvelope
    rw [mul_pow,←pow_mul]
    change 100000*(20000^6*(B+2)^36) ≤ _
    calc
      _ ≤ 100000*(20000^6*X^36) := by gcongr
      _=_ := (Nat.mul_assoc _ _ _).symm
  have ho : 10000*(B+2)^6 ≤ 10000*X^36 := Nat.mul_le_mul_left 10000 ((Nat.pow_le_pow_left hb2 6).trans h6)
  have hf : 6*B*(B+1) ≤ 6*X^36 := by
    calc
      _ ≤ 6*X*X := by gcongr
      _=6*X^2 := by rw [pow_two,Nat.mul_assoc]
      _ ≤ 6*X^36 := Nat.mul_le_mul_left 6 h2
  have hs : B*B ≤ X^36 := (Nat.mul_le_mul hb hb).trans (by simpa only [pow_two] using h2)
  have hA := ha.trans h1
  have hB := hb.trans h1
  have hB1 := hb1.trans h1
  unfold retainedEnvelope
  omega

/-- Positive-depth entry performs paid clearing, the real first head load,
and exact bounded-memory initialization of its assignment cursor. -/
theorem setup_positive (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (a : State 40 896) (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649 = unary s.base) (hr : 0 < s.input.r) :
    ∃ n b, Eval (setupWith loadHead) n a b ∧
      Boundary s F (enter s.key s.input.r 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) b ∧
      n+1 ≤ eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (setupWith loadHead) 0 0) p
        (a.withPC (some (compiled (setupWith loadHead) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧
      ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  have hW := s.source_offset a hm
  obtain ⟨rp,rm,rs,raw,shifted,n,he,ht,hend,hready,hraw,hshift,hspace⟩ :=
    setup_native_run s.input s.source s.ready s.bound s.bounded s.rows s.addressRegisters
      s.dimensionRegisters s.cacheRegisters s.cacheWords s.cache a hm s.base F s.bound hz hr hbound
      (by simpa only [hW] using s.bounded 141) cap.output
  let b := initialControlState a
  let finish := resetGeneratorState (result s.input s.base b rp rm rs raw shifted)
  have hheads : a.stacks 130=unary s.input.r :=
    (hm.stored 130 (by decide)).trans
      ((Native.start_low s.input s.source s.addressRegisters s.dimensionRegisters s.cacheRegisters
        s.cacheWords 130 (by decide)).trans s.ready.colors)
  have hanc := initial_ancestor_storage s.headSize s.key s.input.r s.base (fun i => Fin.elim0 i)
    a hheads hz
  have hleaf : b.regs controllerPorts.leaf=false := by
    rw [(initialControlState_flags a s.input.r hheads).2]
    simp only [Nat.ne_of_gt hr,decide_false]
  have blank (i : Fin 12) (h6 : i≠6) (h9 : i≠9) : b.stacks (tupleStacks i)=[] :=
    initialControlState_tuple a i h6 h9
  have hscan := result_reset_scan_storage s.headSize s.key s.input.r s.base ⟨0,hr⟩
    (fun i => Fin.elim0 i) s.input s.base b rp rm rs raw shifted hanc hleaf
    (by simp only [ProducedSource.headSize,Nat.add_zero])
    (blank 2 (by decide) (by decide)) (blank 3 (by decide) (by decide))
    (blank 4 (by decide) (by decide)) (blank 5 (by decide) (by decide))
    (blank 8 (by decide) (by decide))
  have hnext : ScanBoundary s F ⟨0,hr⟩ (fun i => Fin.elim0 i) 0 finish := by
    refine ⟨hscan,hend,?_,?_,?_⟩
    · apply reset_masters
      exact result_masters s.input s.base b rp rm rs raw shifted s.masters (initialControl_masters a _ hm)
    · constructor
      refine ⟨raw,shifted,?_,?_,?_⟩
      · simpa only [Nat.add_zero] using hraw
      · simpa only [hW] using hshift
      · intro hc
        simpa only [hW,ProducedSource.headSize,Nat.add_zero] using hready
    · rw [reset_result_address649]
      exact hanc.address
  refine ⟨n,finish,he,?_,?_,?_,?_⟩
  · rw [enter_internal s.key s.input.r 0 hr]
    exact Boundary.scan hnext
  · unfold eventPolynomial
    omega
  · intro p q hp hq i
    exact (hspace p q hp hq i).trans (by unfold prefixEnvelope; omega)
  · intro i hi
    rw [reset_persistent _ i hi,result_persistent _ _ _ _ _ _ _ _ i hi]
    exact initialControlState_outside_tuple a i hi.tuple

theorem initial_zero_cursor (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ) (a : State 40 896)
    (hz : levels=0) (hh : a.stacks 130=[]) (ha : a.stacks 649=List.replicate base true) :
    CursorStorage h key levels base
      (enter key levels 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) (initialControlState a) := by
  subst levels
  simpa only [enter_leaf] using
    (CursorStorage.leaf (initial_leaf_storage h key base (fun i => Fin.elim0 i) a hh ha))


/-- With no heads, the real setup reaches one empty-tuple leaf. It preserves
the node base and all query data; the concrete visitor supplies the unit. -/
theorem setup_zero (s : ProducedSource) (F : ℕ) (a : State 40 896)
    (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base) (hr : s.input.r=0) :
    ∃ n b, Eval (setupWith loadHead) n a b ∧
      Boundary s F (enter s.key s.input.r 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) b ∧
      n+1 ≤ eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (setupWith loadHead) 0 0) p
        (a.withPC (some (compiled (setupWith loadHead) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧
      ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  have hheads : a.stacks 130=[] := by
    have hh := (hm.stored 130 (by decide)).trans
      ((Native.start_low s.input s.source s.addressRegisters s.dimensionRegisters s.cacheRegisters
        s.cacheWords 130 (by decide)).trans s.ready.colors)
    change a.stacks (SignatureHeadLoader.lowStacks 130) = unary s.input.r at hh
    have he : SignatureHeadLoader.lowStacks (130 : Fin 768) = (130 : Fin 896) := rfl
    simpa only [he, hr, unary, List.replicate_zero] using hh
  have he := setup_zero_eval loadHead a s.base hheads hz
  have hc := initial_zero_cursor s.headSize s.key s.input.r s.base a hr hheads hz
  have hb := initialControl_endpoint_bound a 0 s.base F hheads hz hbound
  have hnext : Boundary s F
      (enter s.key s.input.r 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) (initialControlState a) := by
    rw [enter,dite_eq_left hr.symm] at hc ⊢
    cases hc with
    | leaf hl =>
      apply Boundary.leaf
      refine ⟨hl,hb,initialControl_masters a _ hm,?_⟩
      intro _
      exact (initialControlState_outside_tuple a 649 (by decide)).trans hz
  have hclear := clearWordsTime_le_on (List.ofFn tupleStacks) a F (fun i _ => hbound i)
  rw [List.length_ofFn] at hclear
  have hbase : s.base ≤ F := by simpa only [hz,unary,List.length_replicate] using hbound 649
  have ht : clearWordsTime (List.ofFn tupleStacks) a+7*s.base+14+1 ≤ 31*F+51 := by omega
  refine ⟨_,initialControlState a,he,hnext,?_,?_,?_⟩
  · unfold eventPolynomial
    omega
  · have hlocal := StructuredSpace.local_stack_bound (compiled (setupWith loadHead) 0 0)
      (a := a.withPC (some (compiled (setupWith loadHead) 0 0).entry))
      (steps := 31*F+51) (StreamResources.dataBits_le_mul _ hbound)
    intro p q hp hq i
    exact (hlocal p q (by omega) hq i).trans (by unfold prefixEnvelope; omega)
  · intro i hi
    exact initialControlState_outside_tuple a i hi.tuple

/-- Setup for the fixed actual DFS, including its zero-head entry. -/
theorem setup_run (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (a : State 40 896) (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base) :
    ∃ n b, Eval (setupWith loadHead) n a b ∧
      Boundary s F (enter s.key s.input.r 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) b ∧
      n+1 ≤ eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (setupWith loadHead) 0 0) p
        (a.withPC (some (compiled (setupWith loadHead) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧
      ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  by_cases hr : s.input.r=0
  · exact setup_zero s F a hbound hm hz hr
  · exact setup_positive s F cap a hbound hm hz (Nat.pos_of_ne_zero hr)

/-- Every nonleaf semantic edge is realized by the concrete installed body.
It preserves every physical query master and the pair accumulator bytes. -/
theorem nonleaf_step (s : ProducedSource) (F leafCost : ℕ) (cap : RetainedCap s F)
    (event : Event s.key s.input.r) (before after : Cursor s.key s.input.r)
    (a : State 40 896) (step : Step s.key s.input.r event before after)
    (ha : Boundary s F before a)
    (hnoleaf : ∀ ancestors,event≠Event.leaf ancestors) :
    a.regs controllerPorts.active=true ∧ ∃ n b,
      Iteration controllerPorts routines n a b ∧ Boundary s F after b ∧
      n+1 ≤ costWeight s.key s.input.r (eventPolynomial s F) leafCost event ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (body controllerPorts routines) 0 0) p
        (a.withPC (some (compiled (body controllerPorts routines) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧
      ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  unfold routines
  cases step with
  | fresh depth ancestors rep =>
    cases ha with
    | scan hs =>
      refine ⟨hs.active,?_⟩
      by_cases hd : depth.val + 1 < s.input.r
      · obtain ⟨n,b,he,hb,ht,hspace,hframe⟩ := fresh_internal_step s F cap
          QueryVisitorProgram.visitor depth ancestors rep a hs hd
        refine ⟨n,b,he,?_,?_,hspace,hframe⟩
        · rw [enter_internal s.key s.input.r (depth.val+1) hd]
          exact Boundary.scan hb
        · simpa only [costWeight,Nat.mul_comm] using ht
      · have hd' : depth.val+1=s.input.r := by have := depth.isLt; omega
        obtain ⟨n,b,he,hb,ht,hspace,hframe⟩ := fresh_final_step s F cap
          QueryVisitorProgram.visitor depth ancestors rep a hs hd'
        exact ⟨n,b,he,hb,by simpa only [costWeight,Nat.mul_comm] using ht,hspace,hframe⟩
  | duplicate depth ancestors candidate hdup =>
    cases ha with
    | scan hs =>
      obtain ⟨n,b,he,hb,ht,hspace,hframe⟩ := duplicate_step s F cap QueryVisitorProgram.visitor
        depth ancestors candidate a hs hdup
      refine ⟨hs.active,n,b,he,Boundary.scan hb,?_,hspace,?_⟩
      · simpa only [costWeight,Nat.mul_comm] using ht
      · intro i hi
        exact hframe i (hi.tuple 2) (hi.tuple 7) hi.not_fresh
  | exhausted depth ancestors =>
    cases ha with
    | scan hs =>
      refine ⟨hs.active,?_⟩
      rcases depth with ⟨depth,hd⟩
      cases depth with
      | zero =>
        obtain ⟨n,b,he,hb,ht,hspace,hframe⟩ := exhausted_root_step s F QueryVisitorProgram.visitor
          ⟨0,hd⟩ ancestors a hs rfl
        exact ⟨n,b,he,Boundary.halt hb,ht,hspace,hframe⟩
      | succ depth =>
        obtain ⟨n,b,he,hb,ht,hspace,hframe⟩ := exhausted_successor_step s F cap
          QueryVisitorProgram.visitor ⟨depth,by omega⟩ hd ancestors a hs
        exact ⟨n,b,he,Boundary.scan hb,ht,hspace,hframe⟩
  | leaf ancestors => exact False.elim (hnoleaf ancestors rfl)

theorem queryMaster_persistent (i : Fin 896) (hi : i∈QueryTupleState.masterPorts) :
    PersistentPort i := by
  simp only [QueryTupleState.masterPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals exact ⟨by decide,by decide,by decide⟩

theorem query_frame_of_persistent (a b : State 40 896)
    (hf : ∀ i,PersistentPort i → b.stacks i=a.stacks i) :
    QueryTupleState.QueryMasterFrame a b :=
  ⟨fun i hi => hf i (queryMaster_persistent i hi)⟩

theorem leafStorage_frame (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ)
    (ancestors : Prefix (Representatives key) levels) (a b : State 40 896)
    (ha : LeafStorage h key levels base ancestors a)
    (hf : ∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i)
    (hr : ∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i)
    (hc : ∀ i∈currentHeadPorts,b.stacks i=[]) :
    LeafStorage h key levels base ancestors b := by
  refine ⟨⟨ha.depth_le,?_,?_,?_,?_,?_⟩,?_,hc⟩
  · exact (hf 836 (by decide)).trans ha.cursors
  · exact (hf 837 (by decide)).trans ha.representatives
  · exact (hf 842 (by decide)).trans ha.heads
  · exact (hf 845 (by decide)).trans ha.address
  · exact (hr 36 (by decide)).trans ha.active
  · exact (hr 37 (by decide)).trans ha.leaf

theorem leafBoundary_frame (s : ProducedSource) (F : ℕ)
    (ancestors : Prefix (Representatives s.key) s.input.r) (a b : State 40 896)
    (ha : LeafBoundary s F ancestors a) (hb : WordBound F b)
    (hm : QueryTupleState.QueryMasterFrame a b)
    (hf : ∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i)
    (hr : ∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i)
    (hc : ∀ i∈currentHeadPorts,b.stacks i=[])
    (hz : s.input.r=0 → b.stacks 649=a.stacks 649) : LeafBoundary s F ancestors b := by
  exact ⟨leafStorage_frame s.headSize s.key s.input.r s.base ancestors a b
    ha.toLeafStorage hf hr hc,hb,source_frame_of_queryFrame s.masters a b ha.masters hm,
    fun hzero => (hz hzero).trans (ha.zero_address649 hzero)⟩

/-- The traversal relation carries the actual ring inputs and the SAME
physical851 dictionary's additive readout together with its cursor state. -/
structure Rel (s : ProducedSource) (F : ℕ) {r Q n d : ℕ}
    (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
    (cursor : Cursor s.key s.input.r) (acc : Truncated (q.p.model.O q.p.t) q.J)
    (a : State 40 896) : Prop where
  boundary : Boundary s F cursor a
  query : QueryTupleState.QueryReady q node H high E U P a
  accumulator : QueryTupleState.PairAccumulatorMeaning q acc a

/-- The actual setup preserves the prepared ring context and the pair
accumulator while installing the first cursor (or the empty tuple leaf). -/
theorem setup_rel_run (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base)
    (hquery : QueryTupleState.QueryReady q node H high E U P a)
    (hacc : QueryTupleState.PairAccumulatorMeaning q acc a) :
    ∃ steps b, Eval (setupWith loadHead) steps a b ∧
      Rel s F q node H high E U P
        (enter s.key s.input.r 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) acc b ∧
      steps+1 ≤ eventPolynomial s F ∧
      ∀ p z,p ≤ steps+1 → Trace (compiled (setupWith loadHead) 0 0) p
        (a.withPC (some (compiled (setupWith loadHead) 0 0).entry)) z →
        ∀ i,(z.stacks i).length ≤ prefixEnvelope s F := by
  obtain ⟨steps,b,he,hb,ht,hspace,hframe⟩ := setup_run s F cap a hbound hm hz
  exact ⟨steps,b,he,⟨hb,hquery.frame (query_frame_of_persistent a b hframe),
    hacc.frame (hframe 851 ⟨by decide,by decide,by decide⟩)⟩,ht,hspace⟩

/-- At completed traversal, the actual root flag is false and low649 again
contains the original node base for the next finite-difference pair. -/
theorem Rel.halted {s : ProducedSource} {F r Q n d : ℕ}
    {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ}
    {acc : Truncated (q.p.model.O q.p.t) q.J} {a : State 40 896}
    (ha : Rel s F q node H high E U P .halt acc a) :
    a.regs controllerPorts.active=false ∧ a.stacks 649=unary s.base := by
  cases ha.boundary with
  | halt hb => exact ⟨hb.active,hb.address649⟩

/-- Exact nonleaf preservation of the enriched arithmetic relation. The
ring/cache words, masks and851 dictionary are transported by actual frames. -/
theorem nonleaf_rel_step (s : ProducedSource) (F leafCost : ℕ) (cap : RetainedCap s F)
    {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
    (value : Prefix (Representatives s.key) s.input.r → Truncated (q.p.model.O q.p.t) q.J)
    (event : Event s.key s.input.r) (before after : Cursor s.key s.input.r)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (step : Step s.key s.input.r event before after)
    (ha : Rel s F q node H high E U P before acc a)
    (hnoleaf : ∀ ancestors,event≠Event.leaf ancestors) :
    a.regs controllerPorts.active=true ∧ ∃ steps b,
      Iteration controllerPorts routines steps a b ∧
      Rel s F q node H high E U P after (acc+callbackWeight s.key s.input.r value event) b ∧
      steps+1 ≤ costWeight s.key s.input.r (eventPolynomial s F) leafCost event ∧
      ∀ p z,p ≤ steps+1 → Trace (compiled (body controllerPorts routines) 0 0) p
        (a.withPC (some (compiled (body controllerPorts routines) 0 0).entry)) z →
        ∀ i,(z.stacks i).length ≤ prefixEnvelope s F := by
  obtain ⟨hactive,steps,b,he,hbound,ht,hspace,hframe⟩ :=
    nonleaf_step s F leafCost cap event before after a step ha.boundary hnoleaf
  have hquery := ha.query.frame (query_frame_of_persistent a b hframe)
  have hpair := ha.accumulator.frame (hframe 851 ⟨by decide,by decide,by decide⟩)
  have hz : callbackWeight s.key s.input.r value event=0 := by
    cases event with
    | candidate => rfl
    | exhausted => rfl
    | leaf ancestors => exact False.elim (hnoleaf ancestors rfl)
  refine ⟨hactive,steps,b,he,?_,ht,hspace⟩
  rw [hz,add_zero]
  exact ⟨hbound,hquery,hpair⟩

/-- Any active concrete cursor has one of the proved semantic steps. The
numeric counter bound excludes both overshoot and a stuck scan state. -/
theorem Rel.enabled {s : ProducedSource} {F r Q n d : ℕ}
    {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ}
    {cursor : Cursor s.key s.input.r} {acc : Truncated (q.p.model.O q.p.t) q.J}
    {a : State 40 896} (ha : Rel s F q node H high E U P cursor acc a)
    (hactive : a.regs controllerPorts.active=true) :
    ∃ event after, Step s.key s.input.r event cursor after :=
  cursor_enabled s.headSize s.key s.input.r s.base cursor a ha.boundary.cursorStorage hactive

/-- An arbitrary derivation of the actual nonleaf body is the same measured
run as its cursor refinement, including every prefix bound. -/
theorem nonleaf_eval_preserves (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
    (value : Prefix (Representatives s.key) s.input.r → Truncated (q.p.model.O q.p.t) q.J)
    (cursor : Cursor s.key s.input.r) (acc : Truncated (q.p.model.O q.p.t) q.J)
    (steps : ℕ) (a b : State 40 896)
    (ha : Rel s F q node H high E U P cursor acc a)
    (hactive : a.regs controllerPorts.active=true)
    (hnoleaf : ∀ ancestors,cursor≠Cursor.leaf ancestors)
    (heval : Eval (body controllerPorts routines) steps a b) :
    (∃ after nextAcc, Rel s F q node H high E U P after nextAcc b) ∧
      ∀ p z,p ≤ steps+1 → Trace (compiled (body controllerPorts routines) 0 0) p
        (a.withPC (some (compiled (body controllerPorts routines) 0 0).entry)) z →
        ∀ i,(z.stacks i).length ≤ prefixEnvelope s F := by
  obtain ⟨event,after,hstep⟩ := ha.enabled hactive
  have hne : ∀ ancestors,event≠Event.leaf ancestors := by
    intro ancestors he
    subst event
    cases hstep with
    | leaf ancestors => exact hnoleaf ancestors rfl
  obtain ⟨_,n',b',hit,hb,_,hspace⟩ :=
    nonleaf_rel_step s F 0 cap q node H high E U P value event cursor after acc a hstep ha hne
  have hn := StreamResources.eval_steps_eq 0 0 heval hit.eval
  have hs := heval.final_unique 0 hit.eval
  subst n'
  subst b'
  exact ⟨⟨after,_,hb⟩,hspace⟩

/-- Program input/output selectors do not alter an internal command trace. -/
theorem prefix_bound_ports (code : Cmd 40 896) (steps bound : ℕ) (a : State 40 896)
    (h : QueryExecution.PrefixBound code steps a bound) :
    ∀ p z,p ≤ steps → Trace (compiled code 0 0) p
      (a.withPC (some (compiled code 0 0).entry)) z →
      ∀ i,(z.stacks i).length ≤ bound := by
  intro p z hp hz i
  exact h.bound p z hp hz i

/-- The empty-head leaf uses the actual unit visitor and actual root return.
The exact addition, time, fixed boundary cap and all-prefix bound share one run. -/
theorem zero_leaf_step (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
    (ancestors : Prefix (Representatives s.key) s.input.r)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (hzero : s.input.r=0) (ha : Rel s F q node H high E U P (.leaf ancestors) acc a)
    (hPF : 4*P+6 ≤ F)
    (hout : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) ≤ F) :
    a.regs controllerPorts.active=true ∧ ∃ steps b,
      Iteration controllerPorts routines steps a b ∧
      Rel s F q node H high E U P .halt
        (acc+Dense.readout (1 : Dense (q.p.model.O q.p.t) q.p.t q.J)) b ∧
      steps+1 ≤ QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J F+
        1600*(F+1)+eventPolynomial s F ∧
      ∀ p z,p ≤ steps+1 → Trace (compiled (body controllerPorts routines) 0 0) p
        (a.withPC (some (compiled (body controllerPorts routines) 0 0).entry)) z →
        ∀ i,(z.stacks i).length ≤ max (prefixEnvelope s F)
          (896*F+QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J F+1600*(F+1)) := by
  unfold routines
  cases hbound : ha.boundary with
  | leaf hl =>
    have hreps : a.stacks 837=[] := by
      change a.stacks (tupleStacks 1)=[]
      rw [hl.representatives]
      simp only [representativeFrames,representativeWords,hzero,List.ofFn_zero,
        List.reverse_nil,suspendedFrames,List.flatMap_nil]
    obtain ⟨nv,b,hvisit,hquery,hacc,hb,hmasters,hframes,hregs,hcurrent,h649,htv,hspacev⟩ :=
      QueryVisitorProgram.visitor_empty ha.query ha.accumulator hl.bound hPF hreps hout
    have hleaf := leafBoundary_frame s F ancestors a b hl hb hmasters hframes hregs hcurrent
      (fun _ => h649)
    obtain ⟨na,c,hasc,hc,hta,hspacea,hframea⟩ := ascend_leaf s F cap ancestors b hleaf
    have hhalt : Boundary s F Cursor.halt c := by
      simpa only [leave_zero s.headSize s.key s.input.r hzero ancestors] using hc
    have hquery' := hquery.frame (query_frame_of_persistent b c hframea)
    have hacc' := hacc.frame (hframea 851 ⟨by decide,by decide,by decide⟩)
    refine ⟨hl.active,nv+na+1,c,Iteration.leaf hl.leaf hvisit hasc,
      ⟨hhalt,hquery',hacc'⟩,by omega,?_⟩
    apply SignatureTupleBranchSpace.leaf_body_prefix_bound loadHead QueryVisitorProgram.visitor
      a b c nv na _ hl.leaf hvisit hasc
    · intro p z hp hz i
      exact (prefix_bound_ports QueryVisitorProgram.visitor _ _ a hspacev p z (by omega) hz i).trans (Nat.le_max_right _ _)
    · intro p z hp hz i
      exact (hspacea p z (by omega) hz i).trans (Nat.le_max_left _ _)

theorem reload_power_bound (F B C X : ℕ) (hX : 1 ≤ X)
    (hF : F ≤ C*X^36) (hB : B+2 ≤ X) :
    (F+B+2)^64 ≤ (C+1)^64*X^2304 := by
  have h36 : X ≤ X^36 := by simpa only [pow_one] using pow_le_pow_right₀ hX (by decide : 1 ≤ 36)
  have hsum : F+B+2 ≤ (C+1)*X^36 := by rw [add_mul,one_mul]; omega
  calc
    _ ≤ ((C+1)*X^36)^64 := Nat.pow_le_pow_left hsum 64
    _=(C+1)^64*X^2304 := by rw [mul_pow,←pow_mul]

/-- The retained cap and all per-event transient budgets use fixed powers
of physical input lengths. The exponent2304 is independent of the input. -/
theorem event_and_prefix_polynomial (s : ProducedSource) (A : ℕ) :
    let C := 100000*20000^6+10050
    let L := 1000*(10000000000000000*HeadLoaderBudgets.sizeCoefficient^8+3)*(C+1)^64
    eventPolynomial s (retainedEnvelope s.bound A) ≤
        (L+4001*C+4000)*((A+s.bound+2)^36)^64 ∧
      prefixEnvelope s (retainedEnvelope s.bound A) ≤
        (L+4001*C+4000)*((A+s.bound+2)^36)^64 := by
  dsimp only
  let C := 100000*20000^6+10050
  let R := 1000*(10000000000000000*HeadLoaderBudgets.sizeCoefficient^8+3)
  let X := A+s.bound+2
  let F := retainedEnvelope s.bound A
  have hX : 1 ≤ X := by dsimp [X]; omega
  have h36 : X^36 ≤ (X^36)^64 := by
    simpa only [pow_one] using pow_le_pow_right₀ (one_le_pow₀ hX : 1 ≤ X^36) (by decide : 1 ≤ 64)
  have h1 : 1 ≤ (X^36)^64 := one_le_pow₀ (one_le_pow₀ hX : 1 ≤ X^36)
  have hF36 : F ≤ C*X^36 := retainedEnvelope_polynomial s.bound A
  have hF : F ≤ C*(X^36)^64 := hF36.trans (Nat.mul_le_mul_left C h36)
  have hbase := reload_power_bound F s.bound C X hX hF36 (by dsimp [X]; omega)
  rw [show (2304 : ℕ)=36*64 from rfl,pow_mul] at hbase
  have hrun : runEnvelope s.bound F ≤ (R*(C+1)^64)*(X^36)^64 := by
    unfold runEnvelope
    calc
      _ ≤ R*((C+1)^64*(X^36)^64) := Nat.mul_le_mul_left R hbase
      _=(R*(C+1)^64)*(X^36)^64 := (Nat.mul_assoc _ _ _).symm
  have hscan : scannerEnvelope s.bound ≤ F := by dsimp [F,retainedEnvelope]; omega
  have hnumeric (scan reload f power c l : ℕ) (hs : scan ≤ f)
      (hf : f ≤ c*power) (hr : reload ≤ l*power) (hp : 1 ≤ power) :
      scan+reload+200*f+200 ≤ (l+4001*c+4000)*power ∧
        4000*(f+1)+reload ≤ (l+4001*c+4000)*power := by
    rw [Nat.add_mul,Nat.add_mul,Nat.mul_assoc 4001 c]
    constructor <;> omega
  exact hnumeric (scannerEnvelope s.bound) (runEnvelope s.bound F) F ((X^36)^64) C
    (R*(C+1)^64) hscan hF hrun h1

theorem prefix_count_positive (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels : ℕ) :
    1 ≤ prefixCount (fun d => Fintype.card (Representatives key d)) levels := by
  classical
  have hp (d : ℕ) : 1 ≤ Fintype.card (Representatives key d) := by
    have hn : 0 < Fintype.card (Representatives key d) := by
      simpa only [Nat.card_eq_fintype_card] using
        AttainedSignatures.card_representative_pos (key d)
          (pow_pos (by decide : 0 < (2 : ℕ)) _)
    omega
  simpa only [prefixCount_zero] using
    prefixCount_le (fun d => Fintype.card (Representatives key d)) (Nat.zero_le levels)
      (fun d _ => hp d)


theorem absorb_leaf_cost (P C r K H leafCost : ℕ) (hP : P ≤ C) (hK : 1 ≤ K)
    (hLeaf : leafCost ≤ C*(r+1)*2^H) :
    (2*P)*r*K*4^H+K*leafCost+1 ≤ (3*C+1)*(r+1)*K*4^H := by
  have hp : 2^H ≤ 4^H := Nat.pow_le_pow_left (by decide) H
  have h4 : 1 ≤ 4^H := one_le_pow₀ (by decide)
  have hleaf : K*leafCost ≤ C*(r+1)*K*4^H := by
    calc
      _ ≤ K*(C*(r+1)*2^H) := Nat.mul_le_mul_left K hLeaf
      _ ≤ K*(C*(r+1)*4^H) := by gcongr
      _=C*(r+1)*K*4^H := by ring
  have hscan : (2*P)*r*K*4^H ≤ (2*C)*(r+1)*K*4^H := by gcongr; omega
  have hone : 1 ≤ (r+1)*K*4^H := by
    simpa only [one_mul] using Nat.mul_le_mul (Nat.mul_le_mul (show 1 ≤ r+1 by omega) hK) h4
  calc
    _ ≤ (2*C)*(r+1)*K*4^H+C*(r+1)*K*4^H+(r+1)*K*4^H := by omega
    _=(3*C+1)*(r+1)*K*4^H := by ring

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
