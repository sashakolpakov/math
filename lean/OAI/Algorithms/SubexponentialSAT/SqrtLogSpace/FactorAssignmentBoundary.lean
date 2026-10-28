import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallbackNative
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
import OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgramZero

/-! The real initializer and paid cache setup establish the physical boundary
for the actual stored-ID fold. Bounds are fixed before that fold; the current
Good-empty-support seed is serialized on151, the unread suffix on150 and the
reversed original ID on149. No execution service is a field below. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
open OAI BitProgram StructuredCalls SubexpSetupStorage
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps MomentsProgram NativeSemantics
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open FactorAssignmentProgram

noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The fixed source masters read by the actual scalar table producer. -/
def scalarPorts : List (Fin 768) :=
  [194,202,203,201,204,145,280,207,78,128,243,138,703]

/-- The fixed layout/source masters read by the actual source-row producer. -/
def sourcePorts : List (Fin 768) :=
  [130,131,132,710,711,140,712,138,139,135,136,713,714,715,717,716,280,207,211,728]

/-- All retained words used at a factor boundary, including the original175
ID stream and actual857 correction word. -/
def retainedPorts : List (Fin 896) :=
  (scalarPorts ++ sourcePorts).map FactorTableProgram.basePort ++
    [175,212,281,700,701,702,704,705,706,707,708,857]

theorem table_entry_written (i : Fin 896) (hi : i ∈ FactorTableProgram.entryPorts) :
    i ∈ FactorTableSpace.writtenPorts := by
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    exact List.mem_append_left _ (List.mem_map.mpr ⟨j,(List.mem_filter.mp hj).1,rfl⟩)
  · exact List.mem_append_right _ hi

/-- Numeric support of the actual relocated source writes. -/
theorem written_bounds (i : Fin 896) (hi : i ∈ FactorTableSpace.writtenPorts) :
    i.val = 62 ∨ (340 ≤ i.val ∧ i.val ≤ 684) ∨
      i.val = 881 ∨ i.val = 882 ∨ (885 ≤ i.val ∧ i.val ≤ 892) := by
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    have hjb := Incidence.mem_workerPorts j |>.mp hj
    unfold FactorTableProgram.basePort
    split_ifs
    all_goals simp only [Fin.coe_ofNat_eq_mod, Fin.val_castAdd]
    all_goals omega
  · simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [Fin.coe_ofNat_eq_mod]

theorem retained_not_entry (i : Fin 896) (hi : i ∈ retainedPorts) :
    i ∉ entryScratch := by
  have small : ∀ i ∈ retainedPorts,
      i ∉ ([149,150,151,159,854] ++ callbackScratch.map lowStack : List (Fin 896)) :=
    List.forall_iff_forall_mem.mp (by decide)
  have outside : ∀ i ∈ retainedPorts,
      i.val ≠ 62 ∧ (i.val < 340 ∨ 684 < i.val) ∧ i.val ≠ 881 ∧ i.val ≠ 882 ∧
        (i.val < 885 ∨ 892 < i.val) := List.forall_iff_forall_mem.mp (by decide)
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · exact small i hi hm
  · have hw := written_bounds i (table_entry_written i hm)
    have ho := outside i hi
    omega

theorem retained_not_cache (i : Fin 896) (hi : i ∈ retainedPorts) :
    i ∉ cachePorts.map lowStack :=
  (List.forall_iff_forall_mem.mp (by decide) : ∀ i ∈ retainedPorts,
    i ∉ cachePorts.map lowStack) i hi

theorem entry_not_cache (i : Fin 896) (hi : i ∈ entryScratch) :
    i ∉ LeafNodeCacheProgram.cachePorts.map lowStack := by
  have small : ∀ i ∈ ([149,150,151,159,854] ++ callbackScratch.map lowStack : List (Fin 896)),
      i ∉ LeafNodeCacheProgram.cachePorts.map lowStack := List.forall_iff_forall_mem.mp (by decide)
  rcases List.mem_append.mp hi with hi | hi
  · exact small i hi
  · intro hm
    have hw := written_bounds i (table_entry_written i hi)
    have hc : i.val < 340 ∧ i.val ≠ 62 :=
      (List.forall_iff_forall_mem.mp (by decide) : ∀ i ∈ LeafNodeCacheProgram.cachePorts.map lowStack,
        i.val < 340 ∧ i.val ≠ 62) i hm
    omega

theorem table_written_entry (i : Fin 896) (hi : i ∈ FactorTableSpace.writtenPorts)
    (h556 : i ≠ 556) : i ∈ entryScratch := by
  apply List.mem_append_right
  rcases List.mem_append.mp hi with hi | hi
  · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨j,List.mem_filter.mpr ⟨hj,?_⟩,rfl⟩
    have hn : j ≠ 556 := by intro he; subst j; exact h556 rfl
    simpa only [decide_eq_true_eq] using hn
  · exact List.mem_append_right _ hi

theorem scalar_frame {t d J R n : ℕ} {model : RingModel.Data d}
    {M : SubexpPreparedQuartic.Modulus 3 t} {cache : RingProgram.ScalarCache 3 t}
    {theta : DensePolynomialProgram.Coeff (baseWidth 3 t) d}
    {a b : State 16 768}
    (h : FactorTableNative.ScalarMasters t model M cache J R theta a n)
    (hf : ∀ i ∈ scalarPorts, b.stacks i = a.stacks i) :
    FactorTableNative.ScalarMasters t model M cache J R theta b n := by
  refine ⟨h.widthPositive,h.zeroCanonical,h.zeroBits,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hf 194 (by decide)]; exact h.modulus
  · rw [hf 202 (by decide)]; exact h.width
  · rw [hf 203 (by decide)]; exact h.zero
  · rw [hf 201 (by decide)]; exact h.table
  · rw [hf 204 (by decide)]; exact h.degree
  · rw [hf 145 (by decide)]; exact h.choicesLength
  · rw [hf 280 (by decide)]; exact h.zeroWord
  · rw [hf 207 (by decide)]; exact h.oneWord
  · rw [hf 78 (by decide)]; exact h.thetaWord
  · rw [hf 128 (by decide)]; exact h.ambientCount
  · rw [hf 243 (by decide)]; exact h.targetCount
  · rw [hf 138 (by decide)]; exact h.radius
  · rw [hf 703 (by decide)]; exact h.highLength

theorem source_frame {r Q d : ℕ} {p : LayoutProgram.SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)}
    {P : OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData (Fin ps.length)
      (OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType r Q 1)} {a b : State 16 768}
    (h : FactorTableNative.SourceMasters p ps P a)
    (hf : ∀ i ∈ sourcePorts, b.stacks i = a.stacks i) :
    FactorTableNative.SourceMasters p ps P b := by
  constructor
  · rw [hf 130 (by decide)]; exact h.colors
  · rw [hf 131 (by decide)]; exact h.nodes
  · rw [hf 132 (by decide)]; exact h.typeWidth
  · rw [hf 710 (by decide)]; exact h.positive
  · rw [hf 711 (by decide)]; exact h.negative
  · rw [hf 140 (by decide)]; exact h.scalarWidth
  · rw [hf 712 (by decide)]; exact h.power
  · exact h.powerNegative
  · rw [hf 138 (by decide)]; exact h.radius
  · rw [hf 139 (by decide)]; exact h.offset
  · rw [hf 135 (by decide)]; exact h.metadata
  · rw [hf 136 (by decide)]; exact h.plans
  · rw [hf 713 (by decide)]; exact h.inverses
  · rw [hf 714 (by decide)]; exact h.negatives
  · rw [hf 715 (by decide)]; exact h.differences
  · rw [hf 717 (by decide)]; exact h.ringWidth
  · rw [hf 716 (by decide)]; exact h.rowWidth
  · rw [hf 280 (by decide)]; exact h.zero
  · rw [hf 207 (by decide)]; exact h.one
  · rw [hf 211 (by decide)]; exact h.minusOne
  · rw [hf 728 (by decide)]; exact h.inverseDenominator

/-- Physical entry facts produced by the actual addressed loader, ring
producer, accepted-head overlay, and the previous accumulator's reset. -/
structure Entry {r Q n d : ℕ} (q : Factor.Spec r Q n d) (P M S : ℕ)
    (a : FactorAssignmentProgram.Data) : Prop where
  scalar : FactorTableNative.ScalarMasters q.p.t q.p.model q.p.modulus q.p.cache q.J q.p.R
    q.theta (projectState localRegister FactorTableProgram.basePort a) n
  masters : FactorTableNative.SourceMasters q.p q.ps q.packing
    (projectState localRegister FactorTableProgram.basePort a)
  incoming : WordBound P a
  copies : ∀ pair ∈ LeafNodeCacheProgram.directCopies,
    (a.stacks (lowStack pair.1)).length ≤ M
  ambientCap : (a.stacks 128).length ≤ M
  oneCap : (a.stacks 207).length ≤ M
  cacheFits : 4*M+6 ≤ P
  seedFits : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J ≤ P
  lowBlank : ∀ i : Fin 56, a.stacks (i.castAdd 840) = []
  width : a.stacks 202 = q.width
  degree : a.stacks 204 = List.replicate d true
  precision : a.stacks 212 = List.replicate q.u true
  minus : q.minus = q.p.minusOne
  digits : a.stacks 281 = IdempotentApplyProgram.triplesTape q.digits
  rows : a.stacks 701 = Encoding.encodeList id q.rawRows
  clauses : a.stacks 700 = Encoding.encodeList id q.clauses
  count : a.stacks 704 = List.replicate q.rawRows.length true
  mark : a.stacks 705 = Encoding.encodeNat q.mark
  flag : a.stacks 706 = [q.marked]
  correction : (a.stacks 857).length = n
  hashWidth : (a.stacks 708).length = q.bitWidth
  hashModulus : BinaryArithmetic.toNat (a.stacks 707) = q.clauses.length
  size : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
    (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S
  radius : q.p.R+1 ≤ Q

/-- The genuine query's physical ring words and the accepted assignment word
supply the scalar producer boundary; its zero law comes from the same model. -/
theorem query_scalar {r Q n d M : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {a : FactorAssignmentProgram.Data}
    (h : QueryTupleState.QueryReady q node H high E U M a)
    (hchoices : (a.stacks 145).length = n) :
    FactorTableNative.ScalarMasters q.p.t q.p.model q.p.modulus q.p.cache q.J q.p.R
      q.theta (projectState localRegister FactorTableProgram.basePort a) n := by
  constructor
  · exact Nat.mul_pos q.p.ht (Nat.zero_lt_succ _)
  · exact q.p.hz
  · exact DensePolynomialProgram.model_zero_bits q.p.t q.p.model q.p.modulus q.p.cache q.p.hz
  · exact h.modulus
  · change (a.stacks 202).length = _
    rw [h.width]
    exact q.widthLength
  · exact h.scalarZero
  · exact h.table
  · change (a.stacks 204).length = d
    rw [h.degree,List.length_replicate]
  · exact hchoices
  · exact h.zero
  · exact h.one
  · exact h.theta
  · exact h.ambient
  · exact h.order
  · exact h.radius
  · change (a.stacks 703).length = n
    rw [h.highBits,List.length_ofFn]

/-- All source-row metadata come from the actual query's retained words. -/
theorem query_source {r Q n d M : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {a : FactorAssignmentProgram.Data}
    (h : QueryTupleState.QueryReady q node H high E U M a) :
    FactorTableNative.SourceMasters q.p q.ps q.packing
      (projectState localRegister FactorTableProgram.basePort a) := by
  refine ⟨h.colors,h.nodes,h.typeWidth,h.positive,h.negative,h.sourceWidth,h.power,
    h.powerNegative,h.radius,h.offset,h.metadata,h.plans,h.inverses,h.negatives,
    h.differences,h.ringWidth,h.rowWidth,h.zero,h.one,?_,h.inverseDenominator⟩
  change a.stacks 211 = RingProgram.flat q.p.minusOne
  rw [h.minus,h.sourceMinus]

/-- The actual query masters, accepted145 overlay and produced low-bank reset
instantiate the assignment boundary. Master cap M and structural cap P remain
separate so setup restores P before every accepted assignment. -/
theorem entry_of_query {r Q n d P M S : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {a : FactorAssignmentProgram.Data}
    (h : QueryTupleState.QueryReady q node H high E U M a)
    (ha : WordBound P a) (hchoices : (a.stacks 145).length = n)
    (hlow : ∀ i : Fin 56, a.stacks (i.castAdd 840) = [])
    (hcache : 4*M+6 ≤ P)
    (hseed : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J ≤ P)
    (hsize : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
      (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S)
    (hradius : q.p.R+1 ≤ Q) : Entry q P M S a := by
  refine ⟨query_scalar h hchoices,query_source h,ha,h.cacheCaps,h.ambientCap,h.oneCap,
    hcache,hseed,hlow,h.width,h.degree,?_,h.sourceMinus,?_,h.rows,h.clauses,
    h.rowCount,h.markedIndex,h.markedFlag,?_,h.indexWidth,h.indexModulus,hsize,hradius⟩
  · rw [h.lifting]
    exact h.precision
  · exact h.code.trans (IdempotentApplyProgram.coefficient_tape q.code)
  · rw [h.inner,List.length_ofFn]

/-- This is the actual prefix of assignment, before copying the ID stream. -/
def prepare : Code := .seq «initialize» setup

def prepareCost (a : FactorAssignmentProgram.Data) : ℕ :=
  initializeCost a + setupCost (initialized a)

/-- Updates of the three actual loop ports preserve every other stack. -/
theorem loop_state_frame {n B d : ℕ} (base : Fin 896 → List Bool)
    (regs : Fin 40 → Bool) (seed : FactorAssignmentLoop.Raw n B d)
    (tail payload : List Bool) (i : Fin 896)
    (h149 : i ≠ 149) (h150 : i ≠ 150) (h151 : i ≠ 151) :
    (FactorAssignmentLoop.state base regs seed tail payload).stacks i = base i := by
  simp only [FactorAssignmentLoop.state, Function.update_of_ne h149,
    Function.update_of_ne h150, Function.update_of_ne h151]

/-- Every parsed record has the same chosen structural bound, independently
of the prior prefix's transient workspace. -/
theorem loop_state_bound {n B d u J P : ℕ} (a : FactorAssignmentProgram.Data)
    (regs : Fin 40 → Bool) (seed : FactorAssignmentLoop.Raw n B d)
    (tail : List Bool) (f : ℕ) (ha : WordBound P a)
    (hseed : NativeSemantics.Good ∅ u J seed)
    (hcapacity : FactorAssignmentLoop.byteBound n B d u J ≤ P)
    (htail : tail.length ≤ P) (hf : f+1 ≤ P) :
    WordBound P (FactorAssignmentLoop.state a.stacks regs seed tail
      (Encoding.encodeNat f).reverse) := by
  have hs : (Product.bytes seed).length ≤ P :=
    (TruncatedRingProgram.empty_bytes_length_le (a := seed) ⟨hseed.valid,hseed.nodup⟩).trans hcapacity
  intro i
  by_cases hi149 : i = 149
  · subst i
    simpa only [FactorAssignmentLoop.state, Function.update_self, List.length_reverse,
      Encoding.length_encodeNat] using hf
  by_cases hi150 : i = 150
  · subst i
    simpa only [FactorAssignmentLoop.state, Function.update_of_ne (by decide : (150 : Fin 896) ≠ 149),
      Function.update_self] using htail
  by_cases hi151 : i = 151
  · subst i
    simpa only [FactorAssignmentLoop.state, Function.update_of_ne (by decide : (151 : Fin 896) ≠ 149),
      Function.update_of_ne (by decide : (151 : Fin 896) ≠ 150), Function.update_self] using hs
  rw [loop_state_frame _ _ _ _ _ i hi149 hi150 hi151]
  exact ha i

/-- Physical prepared-store facts, with no evaluator, layout service, or
query result among the fields. The mutable149/150/151 fields are supplied by
the concrete record reader and current Good-empty-support accumulator. -/
structure Ready {r Q n d : ℕ} (q : Factor.Spec r Q n d) (P S : ℕ)
    (one : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (a : FactorAssignmentProgram.Data) : Prop where
  scalar : FactorTableNative.ScalarMasters q.p.t q.p.model q.p.modulus q.p.cache q.J q.p.R
    q.theta (projectState localRegister FactorTableProgram.basePort a) n
  masters : FactorTableNative.SourceMasters q.p q.ps q.packing
    (projectState localRegister FactorTableProgram.basePort a)
  incoming : ∀ i, (a.stacks i).length ≤ P
  size : 1029*P+99+n+n*FactorTableProgram.literalRecordBound n
    (FactorTableNative.specializedPayloadBound n q.u q.J (baseWidth 3 q.p.t) d)+1 ≤ S
  radius : q.p.R+1 ≤ Q
  rows : a.stacks 701 = Encoding.encodeList id q.rawRows
  clauses : a.stacks 700 = Encoding.encodeList id q.clauses
  count : a.stacks 704 = List.replicate q.rawRows.length true
  mark : a.stacks 705 = Encoding.encodeNat q.mark
  flag : a.stacks 706 = [q.marked]
  blank : ∀ i ∈ callbackScratch, a.stacks (lowStack i) = []
  tableBlank : ∀ i ∈ FactorTableSpace.writtenPorts, i ≠ 62 → i ≠ 556 → a.stacks i = []
  correction : (a.stacks 857).length = n
  hashWidth : (a.stacks 708).length = q.bitWidth
  hashModulus : BinaryArithmetic.toNat (a.stacks 707) = q.clauses.length
  ringShape : (a.stacks 280).length = d * baseWidth 3 q.p.t
  low : ∀ i : Fin 56, a.stacks (lowStack (Factor.nativeStacks (Memory.lowPort i))) =
    low q.ctx i
  oneBytes : a.stacks 69 = Product.bytes one
  minusBytes : a.stacks 76 = RingProgram.flat q.minus
  tape : a.stacks 143 = IdempotentApplyProgram.triplesTape q.digits
  shape : (a.stacks 88).length = n
  clauseOutput : a.stacks 63 = []
  clauseWork : ∀ i ∈ FactorServices.clauseScratch,
    a.stacks (lowStack (Clause.callerStacks i)) = []
  seedFits : FactorAssignmentLoop.byteBound n (baseWidth 3 q.p.t) d q.u q.J ≤ P

variable {r Q n d P M S : ℕ} {q : Factor.Spec r Q n d}
  {one : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d}
  {a : FactorAssignmentProgram.Data}

theorem Ready.input (h : Ready q P S one a)
    (regs : Fin 40 → Bool) (seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (tail : List Bool) (f : ℕ) (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (htail : tail.length ≤ P) (hf : f+1 ≤ P) :
    FactorAssignmentCallback.Input q P S one seed
      (FactorAssignmentLoop.state a.stacks regs seed tail (Encoding.encodeNat f).reverse) f := by
  let b := FactorAssignmentLoop.state a.stacks regs seed tail (Encoding.encodeNat f).reverse
  have frame (i : Fin 896) (h149 : i ≠ 149) (h150 : i ≠ 150) (h151 : i ≠ 151) :
      b.stacks i = a.stacks i := loop_state_frame _ _ _ _ _ i h149 h150 h151
  have localFrame (i : Fin 768)
      (hi : i ∈ scalarPorts ∨ i ∈ sourcePorts) :
      (projectState localRegister FactorTableProgram.basePort b).stacks i =
        (projectState localRegister FactorTableProgram.basePort a).stacks i := by
    have hn := (List.forall_iff_forall_mem.mp (by decide) : ∀ i ∈ scalarPorts ++ sourcePorts,
      FactorTableProgram.basePort i ≠ 149 ∧ FactorTableProgram.basePort i ≠ 150 ∧
      FactorTableProgram.basePort i ≠ 151) i (List.mem_append.mpr hi)
    exact frame _ hn.1 hn.2.1 hn.2.2
  refine ⟨scalar_frame h.scalar (fun i hi => localFrame i (Or.inl hi)),
    source_frame h.masters (fun i hi => localFrame i (Or.inr hi)),
    loop_state_bound a regs seed tail f h.incoming hseed h.seedFits htail hf,
    h.size,h.radius,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (frame 701 (by decide) (by decide) (by decide)).trans h.rows
  · exact (frame 700 (by decide) (by decide) (by decide)).trans h.clauses
  · exact (frame 704 (by decide) (by decide) (by decide)).trans h.count
  · exact (frame 705 (by decide) (by decide) (by decide)).trans h.mark
  · exact (frame 706 (by decide) (by decide) (by decide)).trans h.flag
  · simp only [FactorAssignmentLoop.state, Function.update_self]
  · simp only [FactorAssignmentLoop.state,
      Function.update_of_ne (by decide : (151 : Fin 896) ≠ 149),
      Function.update_of_ne (by decide : (151 : Fin 896) ≠ 150), Function.update_self]
  · intro i hi
    have hn := (List.forall_iff_forall_mem.mp (by decide) : ∀ i ∈ callbackScratch,
      lowStack i ≠ 149 ∧ lowStack i ≠ 150 ∧ lowStack i ≠ 151) i hi
    exact (frame _ hn.1 hn.2.1 hn.2.2).trans (h.blank i hi)
  · intro i hi h62 h556
    have ne (j : Fin 896) (hj : j.val < 340 ∧ j ≠ 62) : i ≠ j := by
      intro he
      subst i
      exact FactorTableSpace.caller_port_not_written j (Or.inl hj) hi
    exact (frame i (ne 149 (by decide)) (ne 150 (by decide))
      (ne 151 (by decide))).trans (h.tableBlank i hi h62 h556)
  · rw [frame 857 (by decide) (by decide) (by decide)]; exact h.correction
  · rw [frame 708 (by decide) (by decide) (by decide)]; exact h.hashWidth
  · rw [frame 707 (by decide) (by decide) (by decide)]; exact h.hashModulus
  · rw [frame 280 (by decide) (by decide) (by decide)]; exact h.ringShape
  · intro i
    have hn : lowStack (Factor.nativeStacks (Memory.lowPort i)) ≠ 149 ∧
        lowStack (Factor.nativeStacks (Memory.lowPort i)) ≠ 150 ∧
        lowStack (Factor.nativeStacks (Memory.lowPort i)) ≠ 151 := by
      have hi := i.isLt
      have hv : (lowStack (Factor.nativeStacks (Memory.lowPort i))).val = i.val := rfl
      constructor
      · intro he
        have hh := congrArg Fin.val he
        rw [hv] at hh
        norm_num at hh
        omega
      constructor
      · intro he
        have hh := congrArg Fin.val he
        rw [hv] at hh
        norm_num at hh
        omega
      · intro he
        have hh := congrArg Fin.val he
        rw [hv] at hh
        norm_num at hh
        omega
    exact (frame _ hn.1 hn.2.1 hn.2.2).trans (h.low i)
  · exact (frame 69 (by decide) (by decide) (by decide)).trans h.oneBytes
  · exact (frame 76 (by decide) (by decide) (by decide)).trans h.minusBytes
  · exact (frame 143 (by decide) (by decide) (by decide)).trans h.tape
  · rw [frame 88 (by decide) (by decide) (by decide)]; exact h.shape
  · exact (frame 63 (by decide) (by decide) (by decide)).trans h.clauseOutput
  · intro i hi
    have hn := (List.forall_iff_forall_mem.mp (by decide) : ∀ i ∈ FactorServices.clauseScratch,
      lowStack (Clause.callerStacks i) ≠ 149 ∧ lowStack (Clause.callerStacks i) ≠ 150 ∧
      lowStack (Clause.callerStacks i) ≠ 151) i hi
    exact (frame _ hn.1 hn.2.1 hn.2.2).trans (h.clauseWork i hi)


/-- The same fixed initializer/cache command constructs every prepared fact
used by the concrete callback. The fixed boundary P is restored on return. -/
theorem Entry.prepare (h : Entry q P M S a) :
    ∃ b, Eval prepare (prepareCost a) a b ∧
      Ready q P S (oneEntries (n := n) q.p.ops.oneRun.1) b ∧
      NativeSemantics.Good ∅ q.u q.J (oneEntries (n := n) q.p.ops.oneRun.1) ∧
      TruncatedRingProgram.rawDenote q.p.ops.decode (oneEntries (n := n) q.p.ops.oneRun.1) =
        Squarefree.canonical q.u q.J 1 ∧
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode
        (oneEntries (n := n) q.p.ops.oneRun.1) = 1 ∧
      (∀ i ∈ retainedPorts, b.stacks i = a.stacks i) ∧
      (∀ i ∈ ([149,150,151,159,854] : List (Fin 896)), b.stacks i = []) := by
  let a0 := initialized a
  have initFrame (i : Fin 896) (hi : i ∈ retainedPorts) : a0.stacks i = a.stacks i := by
    rw [initialized_stacks, ite_eq_right (retained_not_entry i hi)]
  have scalarMem (i : Fin 768) (hi : i ∈ scalarPorts) :
      FactorTableProgram.basePort i ∈ retainedPorts :=
    List.mem_append_left _ (List.mem_map.mpr ⟨i,List.mem_append_left _ hi,rfl⟩)
  have sourceMem (i : Fin 768) (hi : i ∈ sourcePorts) :
      FactorTableProgram.basePort i ∈ retainedPorts :=
    List.mem_append_left _ (List.mem_map.mpr ⟨i,List.mem_append_right _ hi,rfl⟩)
  have hscalar := scalar_frame (b := projectState localRegister FactorTableProgram.basePort a0)
    h.scalar (fun i hi => initFrame _ (scalarMem i hi))
  have hmasters := source_frame (b := projectState localRegister FactorTableProgram.basePort a0)
    h.masters (fun i hi => initFrame _ (sourceMem i hi))
  have hlow : ∀ i : Fin 56, a0.stacks (i.castAdd 840) = [] := by
    intro i
    rw [initialized_stacks]
    split_ifs
    · rfl
    · exact h.lowBlank i
  have hn : (a0.stacks 128).length = n := by
    rw [show a0.stacks 128 = List.replicate n true from hscalar.ambientCount]
    simp
  obtain ⟨b,he,hlo,hunit,hgood,hraw,hdense,hminus,hminusValue,hdigits,hshape,htable,hframe⟩ :=
    FactorTableDenotation.setup_source_context q.p n q.u q.J q.hu q.hJ q.width
      q.widthLength q.digits a0 hlow hn hscalar.modulus
      ((initFrame 202 (by decide)).trans h.width) hscalar.zero hscalar.table
      ((initFrame 204 (by decide)).trans h.degree)
      ((initFrame 212 (by decide)).trans h.precision) hscalar.targetCount hscalar.oneWord
      hmasters.minusOne ((initFrame 281 (by decide)).trans h.digits)
  have frame (i : Fin 896) (hi : i ∈ retainedPorts) : b.stacks i = a.stacks i :=
    (hframe i (retained_not_cache i hi)).trans (initFrame i hi)
  have hinit : WordBound P a0 := initialized_wordBound a P h.incoming
  have shrink (i : Fin 896) : (a0.stacks i).length ≤ (a.stacks i).length := by
    rw [initialized_stacks]
    split_ifs
    · simp
    · exact le_rfl
  obtain ⟨c,hec,hbound,_⟩ := setup_eval_wordBound_max a0 P M hinit
    (fun pair hp => (shrink (lowStack pair.1)).trans (h.copies pair hp))
    ((shrink 128).trans h.ambientCap) ((shrink 207).trans h.oneCap)
  have hcb : c = b := Eval.final_unique 0 hec he
  have hb : WordBound P b := by
    simpa only [hcb,max_eq_left h.cacheFits] using hbound
  obtain ⟨z,hez,hcache,hhigh⟩ := setup_eval a0
  have hzb : z = b := Eval.final_unique 0 hez he
  have empty (i : Fin 896) (hi : i ∈ entryScratch) : b.stacks i = [] := by
    have hi0 : a0.stacks i = [] := by rw [initialized_stacks, ite_eq_left hi]
    have hnot : i ∉ LeafNodeCacheProgram.cachePorts.map lowStack := entry_not_cache i hi
    by_cases hlt : i.val < 768
    · let j : Fin 768 := ⟨i.val,hlt⟩
      have hj : lowStack j = i := Fin.ext rfl
      have hn : j ∉ LeafNodeCacheProgram.cachePorts := by
        intro hm
        exact hnot (List.mem_map.mpr ⟨j,hm,hj⟩)
      rw [← hzb,← hj,hcache j,LeafNodeCacheProgram.cache_frame _ j hn,
        cacheStart,clearMany_stacks]
      split_ifs
      · rfl
      · exact hi0
    · rw [← hzb,hhigh i (by omega)]
      exact hi0
  have hready : Ready q P S (oneEntries (n := n) q.p.ops.oneRun.1) b := by
    refine ⟨scalar_frame h.scalar (fun i hi => frame _ (scalarMem i hi)),
      source_frame h.masters (fun i hi => frame _ (sourceMem i hi)),hb,h.size,h.radius,
      ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hunit,?_,hdigits,hshape,?_,?_,h.seedFits⟩
    · exact (frame 701 (by decide)).trans h.rows
    · exact (frame 700 (by decide)).trans h.clauses
    · exact (frame 704 (by decide)).trans h.count
    · exact (frame 705 (by decide)).trans h.mark
    · exact (frame 706 (by decide)).trans h.flag
    · intro i hi
      exact empty (lowStack i) (List.mem_append_left _
        (List.mem_append_right _ (List.mem_map.mpr ⟨i,hi,rfl⟩)))
    · intro i hi h62 h556
      exact empty i (table_written_entry i hi h556)
    · rw [frame 857 (by decide)]; exact h.correction
    · rw [frame 708 (by decide)]; exact h.hashWidth
    · rw [frame 707 (by decide)]; exact h.hashModulus
    · rw [frame 280 (by decide)]
      rw [show a.stacks 280 = RingProgram.flat q.p.ops.zeroRun.1 from h.scalar.zeroWord,
        RingProgram.flat_length]
    · intro i
      exact hlo i
    · exact hminus.trans (congrArg RingProgram.flat h.minus.symm)
    · exact empty 63 (by decide)
    · intro i hi
      exact empty _ ((List.forall_iff_forall_mem.mp (by decide) : ∀ i ∈ FactorServices.clauseScratch,
        lowStack (Clause.callerStacks i) ∈ entryScratch) i hi)
  exact ⟨b,(initialize_eval a).seq he,hready,hgood,hraw,hdense,frame,
    fun i hi => empty i (List.mem_append_left _ (List.mem_append_left _ hi))⟩

/-- Initialization and cache reconstruction cost one fixed linear polynomial
in the structural boundary, independently of the number of factor records. -/
theorem prepareCost_le (a : FactorAssignmentProgram.Data) (P : ℕ) (ha : WordBound P a) :
    prepareCost a ≤ entryScratch.length * (2*P+3) + 1100*(P+1) + 2 := by
  have hi := initializeCost_le a P ha
  have hs := setupCost_le (initialized a) P (initialized_wordBound a P ha)
  unfold prepareCost
  omega


/-- The running record ports are disjoint from all three assignment masters.
Thus every factor value is read from the same actual accepted assignment. -/
theorem loop_value (a : FactorAssignmentProgram.Data) (regs : Fin 40 → Bool)
    (seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (tail payload : List Bool) (f : ℕ) :
    q.value ((FactorAssignmentLoop.state a.stacks regs seed tail payload).stacks ∘ lowStack) f =
      q.value (a.stacks ∘ lowStack) f := by
  have hj (j : ℕ) : Factor.factorJet q.p q.ps q.packing n f j q.theta
      ((FactorAssignmentLoop.state a.stacks regs seed tail payload).stacks ∘ lowStack) =
      Factor.factorJet q.p q.ps q.packing n f j q.theta (a.stacks ∘ lowStack) := by
    apply Factor.factorJet_frame
    all_goals exact loop_state_frame _ _ _ _ _ _ (by decide) (by decide) (by decide)
  unfold Factor.Spec.value Factor.Semantics.hashValue Factor.Semantics.markedValue
  simp_rw [hj]

/-- The actual prepared store instantiates the callback used by the record
fold. The output witness, polynomial cost, exact frame and semantic product
all refer to this one fixed callback run. -/
theorem Ready.callback_eval (h : Ready q P S one a)
    (hone : NativeSemantics.Good ∅ q.u q.J one)
    (honeval : TruncatedRingProgram.rawDenote q.p.ops.decode one =
      Squarefree.canonical q.u q.J 1)
    (regs : Fin 40 → Bool) (seed : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d)
    (tail : List Bool) (f width Z : ℕ)
    (hseed : NativeSemantics.Good ∅ q.u q.J seed)
    (htail : tail.length ≤ P) (hf : f+1 ≤ P)
    (hwidth : ∀ hi : f < q.rows.length,
      ∀ w ∈ HashInputProgram.Expansion.weightedRow q.p.t d q.source q.rows[f],
        w.literals.length ≤ width)
    (hZ : 1 ≤ Z) (hP : P ≤ Z) (hbit : q.bitWidth ≤ Z)
    (hshape : d*baseWidth 3 q.p.t ≤ Z)
    (hhashScale : ∀ hi : f < q.rows.length,
      FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
        width q.rows[f].length q.digits.length ≤ Z)
    (hmarkScale : FactorEvaluationSpace.inputScale (baseWidth 3 q.p.t) d n q.u q.J
      q.markedClause.length 0 0 ≤ Z) :
    ∃ out : FactorAssignmentLoop.Raw n (baseWidth 3 q.p.t) d,
      NativeSemantics.Good ∅ q.u q.J out ∧
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode out =
        TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode seed *
          QueryEvaluation.specializeDense q.u q.J
            (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
            (q.value (a.stacks ∘ lowStack) f) ∧
      ∃ steps ≤ FactorAssignmentCallback.uniformCallbackBudget q P S Z, ∃ rr,
        Eval FactorAssignmentProgram.callback steps
          (FactorAssignmentLoop.state a.stacks regs seed tail (Encoding.encodeNat f).reverse)
          (FactorAssignmentLoop.state a.stacks rr out tail []) ∧
        rr 13 = false ∧ rr 14 = true ∧ rr 15 = false := by
  let b := FactorAssignmentLoop.state a.stacks regs seed tail (Encoding.encodeNat f).reverse
  have hi := h.input regs seed tail f hseed htail hf
  obtain ⟨out,rf,steps,z,hout,hvalue,hsteps,he,hframe,h13,h14,h15⟩ :=
    FactorAssignmentCallback.callback_eval_correct hi hone hseed honeval width hwidth
  have hcost := FactorAssignmentCallback.callbackBudget_le hi width Z hZ hP hbit
    hshape hhashScale hmarkScale rf
  have heq := FactorAssignmentCallback.result_eq_state a.stacks regs seed out tail
    (Encoding.encodeNat f).reverse z hframe
  refine ⟨out,hout,?_,steps,hsteps.trans hcost,z.regs,?_,h13,h14,h15⟩
  · have hmask : b.stacks 857 = a.stacks 857 :=
      loop_state_frame _ _ _ _ _ 857 (by decide) (by decide) (by decide)
    have hvalueFrame : q.value (b.stacks ∘ lowStack) f = q.value (a.stacks ∘ lowStack) f :=
      loop_value a regs seed tail (Encoding.encodeNat f).reverse f
    calc
      TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode out =
          TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode seed *
            QueryEvaluation.specializeDense q.u q.J
              (fun v => decide (v ∈ Squarefree.decodeMask n (b.stacks 857)))
              (q.value (b.stacks ∘ lowStack) f) := hvalue
      _ = TruncatedRingProgram.rawValue q.u q.J q.p.ops.decode seed *
            QueryEvaluation.specializeDense q.u q.J
              (fun v => decide (v ∈ Squarefree.decodeMask n (a.stacks 857)))
              (q.value (a.stacks ∘ lowStack) f) := by rw [hmask, hvalueFrame]
  · rw [heq] at he
    exact he

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentBoundary
