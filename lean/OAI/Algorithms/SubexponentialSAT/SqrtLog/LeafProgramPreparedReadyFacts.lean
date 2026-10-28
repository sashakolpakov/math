import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyClean

namespace OAI.Algorithms

/-! Pure post-preparation words imply factor readiness after the actual
assignment setup. Sizes are supplied by the reachable storage proof. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open PerturbationAssembly SubexpSetupStorage MomentsProgram
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes LayoutProgram
open HashCircuitProgram HashCircuitProgram.Native IdempotentApplyProgram.Steps
attribute [local simp] Fin.coe_ofNat_eq_mod

structure NodeFacts {r Q n d : ℕ} (q : Factor.Spec r Q n d)
    (high : Fin 768 → List Bool) : Prop where
  source : SourceMasters q.p q.ps q.packing (FactorReady.baseData high)
  clean : ∀ i,blankPort i → high i=[]
  modulus : high 194=q.p.modulus.bits
  width : high 202=q.width
  scalarZero : high 203=q.p.cache.zero.val
  table : high 201=RingTriple.tableEncoding (HornerProgram.modelTable q.p.t q.p.model q.p.modulus q.p.cache)
  degree : high 204=List.replicate d true
  theta : high 78=RingProgram.flat q.theta
  target : high 243=List.replicate q.J true
  ambient : high 128=List.replicate n true
  highLength : (high 703).length=n
  rows : high 701=Encoding.encodeList id q.rawRows
  clauses : high 700=Encoding.encodeList id q.clauses
  count : high 704=List.replicate q.rawRows.length true
  mark : high 705=Encoding.encodeNat q.mark
  flag : high 706=[q.marked]
  hashWidth : (high 708).length=q.bitWidth
  hashModulus : BinaryArithmetic.toNat (high 707)=q.clauses.length
  one : high 69=Product.bytes q.one
  minus : high 76=RingProgram.flat q.minus
  tape : high 143=IdempotentApplyProgram.triplesTape q.digits
  shape : (high 88).length=n

variable {r Q n d S A : ℕ} {q : Factor.Spec r Q n d}
    {high : Fin 768 → List Bool}

 theorem NodeFacts.assignment_clean (h : NodeFacts q high) (i : Fin 768)
    (hi : blankPort i) (hs : i∉([145,146,147,148] : List (Fin 768))) :
    assignmentBase q (List.replicate d true) high i=[] := by
  have hl : 56 ≤ i.val := by rcases hi with hi|hi|hi <;> omega
  have hc : ¬FactorLoop.collectorTape i := by
    intro hm
    simp only [FactorLoop.collectorTape,List.mem_cons,List.mem_nil_iff,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [blankPort] at hi
  exact (assignment_fixed q _ high i hl hs hc).trans (h.clean i hi)

 theorem NodeFacts.caller (h : NodeFacts q high) (hx : (high 174).length=n) :
    CallerInput q.p.t q.p.model q.p.modulus q.p.cache q.J q.p.R q.theta
      (FactorReady.baseData (assignmentBase q (List.replicate d true) high)) n := by
  have hf := assignment_fixed q (List.replicate d true) high
  have hm := source_masters_assignment q (List.replicate d true) high h.source
  constructor
  · unfold baseWidth; exact Nat.mul_pos q.p.ht (by omega)
  · exact q.p.hz
  · exact DensePolynomialProgram.model_zero_bits q.p.t q.p.model q.p.modulus q.p.cache q.p.hz
  · exact (hf _ (by decide) (by decide) (by decide)).trans h.modulus
  · change (assignmentBase q (List.replicate d true) high 202).length=_
    rw [hf 202 (by decide) (by decide) (by decide),h.width]; exact q.widthLength
  · exact (hf _ (by decide) (by decide) (by decide)).trans h.scalarZero
  · exact (hf _ (by decide) (by decide) (by decide)).trans h.table
  · change (assignmentBase q (List.replicate d true) high 204).length=_
    rw [hf 204 (by decide) (by decide) (by decide),h.degree]; simp
  · exact (assignment_choices q _ high).trans hx
  · exact hm.zero
  · exact hm.one
  · exact (hf _ (by decide) (by decide) (by decide)).trans h.theta
  · exact (hf _ (by decide) (by decide) (by decide)).trans h.ambient
  · exact (hf _ (by decide) (by decide) (by decide)).trans h.target
  · exact hm.radius
  · change (assignmentBase q (List.replicate d true) high 703).length=_
    rw [hf 703 (by decide) (by decide) (by decide)]; exact h.highLength
  · intro i hl hu _
    exact h.assignment_clean i (Or.inr (Or.inr ⟨hl,by omega⟩)) (by
      simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
      refine ⟨?_,?_,?_,?_⟩ <;> intro he <;> subst i <;> norm_num at hl)

 theorem NodeFacts.input (h : NodeFacts q high) (hx : (high 174).length=n)
    (hsize : ∀ i,(assignmentBase q (List.replicate d true) high i).length ≤ A)
    (hstage : WordBound A (Incidence.staged
      (FactorReady.baseData (assignmentBase q (List.replicate d true) high))))
    (hAS : A ≤ S) (harray : (q.p.R+1)*(d*baseWidth 3 q.p.t) ≤ S)
    (hcount : q.p.R+1 ≤ S)
    (hmeta : ∀ x,LayoutProgram.SourceBank.MetadataBound
      (PackingMetadata.value q.packing CollisionProgram.encodeType x) S)
    (hinc : q.ps.length ≤ S) :
    FactorReady.Input q S A (assignmentBase q (List.replicate d true) high) := by
  have hf := assignment_fixed q (List.replicate d true) high
  have hc := h.caller hx
  have he := h.assignment_clean
  have hs := source_of_staged hc
    (source_masters_assignment q (List.replicate d true) high h.source)
    (he 556 (by decide) (by decide)) (he 684 (by decide) (by decide))
    (by intro i hi
        simp only [SourceStaging.backupPorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl
        · exact he 680 (by decide) (by decide)
        · exact he 681 (by decide) (by decide)
        · exact he 682 (by decide) (by decide)
        · exact he 683 (by decide) (by decide))
    (fun i=>(hstage i).trans hAS) harray hcount hmeta hinc
  refine ⟨hc,hs,hsize,hstage,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    assignment_low q _ high rfl,?_,?_,?_,?_,?_,?_⟩
  · exact (hf _ (by decide) (by decide) (by decide)).trans h.rows
  · exact (hf _ (by decide) (by decide) (by decide)).trans h.clauses
  · exact (hf _ (by decide) (by decide) (by decide)).trans h.count
  · exact (hf _ (by decide) (by decide) (by decide)).trans h.mark
  · exact (hf _ (by decide) (by decide) (by decide)).trans h.flag
  · intro i hi
    simp only [FactorDispatch.scratch,List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> (apply he <;> decide)
  · intro i hi
    simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> (apply he <;> decide)
  · rw [hf 708 (by decide) (by decide) (by decide)]; exact h.hashWidth
  · rw [hf 707 (by decide) (by decide) (by decide)]; exact h.hashModulus
  · intro i hi
    simp only [Expansion.scratch,List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> (apply he <;> decide)
  · exact he 358 (by decide) (by decide)
  · exact he 359 (by decide) (by decide)
  · exact (hf _ (by decide) (by decide) (by decide)).trans h.one
  · exact (hf _ (by decide) (by decide) (by decide)).trans h.minus
  · exact (hf _ (by decide) (by decide) (by decide)).trans h.tape
  · rw [hf 88 (by decide) (by decide) (by decide)]; exact h.shape
  · intro i hi
    simp only [FactorServices.indicatorScratch,List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      (apply he <;> decide)
  · intro i hi
    simp only [FactorServices.clauseScratch,List.mem_cons,List.mem_nil_iff,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> (apply he <;> decide)

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
