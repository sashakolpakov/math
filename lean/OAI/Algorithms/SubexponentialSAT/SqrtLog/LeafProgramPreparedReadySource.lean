import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorReadyInput

namespace OAI.Algorithms

/-! The incidence stage supplies the entire local source bank from immutable
source masters. This lemma contains no execution or per-literal premise. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open PerturbationAssembly LayoutProgram SubexpSetupStorage
open SubexponentialSAT.Subexp SubexponentialSAT.Subexp.ConstructivePacking SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

structure SourceMasters {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (a : SourceReady.Data) : Prop where
  colors : a.stacks 130=List.replicate r true
  nodes : a.stacks 131=List.replicate Q true
  typeWidth : a.stacks 132=List.replicate (Q*r) true
  positive : a.stacks 710=p.saved.hp
  negative : a.stacks 711=p.saved.hn
  scalarWidth : a.stacks 140=p.width
  power : a.stacks 712=p.power.1
  powerNegative : p.power.2=[]
  radius : a.stacks 138=List.replicate p.R true
  offset : a.stacks 139=p.aWord
  metadata : a.stacks 135=SelectorProgram.rawRecords
    (PackingMetadata.records P (fun v=>List.replicate v.val true) CollisionProgram.encodeType)
  plans : a.stacks 136=LayoutOwnerFiberProgram.stream ps
  inverses : a.stacks 713=(List.ofFn (fun i=>RingProgram.flat (p.inverse i))).flatten
  negatives : a.stacks 714=(List.ofFn (fun i=>RingProgram.flat (p.negative i))).flatten
  differences : a.stacks 715=(List.ofFn (fun i=>
    (List.ofFn (fun j=>RingProgram.flat (p.difference i j))).flatten)).flatten
  ringWidth : a.stacks 717=p.ringWidth
  rowWidth : a.stacks 716=p.rowWidth
  zero : a.stacks 280=RingProgram.flat p.ops.zeroRun.1
  one : a.stacks 207=RingProgram.flat p.ops.oneRun.1
  minusOne : a.stacks 211=RingProgram.flat p.minusOne
  inverseDenominator : a.stacks 728=RingProgram.flat p.invDenom

theorem staged_external (a : SourceReady.Data) (i : Fin 768)
    (hi : i.val < 340 ∨ 680 ≤ i.val) : (Incidence.staged a).stacks i=a.stacks i := by
  apply Incidence.staged_frame
  · intro he; subst i; norm_num at hi
  · intro p hp
    have hb : 340 ≤ p.2.val ∧ p.2.val < 680 := by
      simp only [Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    intro he
    subst i
    omega

variable {r Q d n J S : ℕ} {p : SourceBank.Parameters r Q d}
    {ps : List (ℕ × ℕ)} {P : PackingData (Fin ps.length) (UniversalType r Q 1)}
    {a : SourceReady.Data} {theta : DensePolynomialProgram.Coeff (baseWidth 3 p.t) d}

theorem source_of_staged (h : CallerInput p.t p.model p.modulus p.cache J p.R theta a n)
    (hm : SourceMasters p ps P a)
    (hf : a.stacks 556=[]) (htmp : a.stacks 684=[])
    (hback : ∀ i∈SourceStaging.backupPorts,a.stacks i=[])
    (hsize : WordBound S (Incidence.staged a))
    (harray : (p.R+1)*(d*baseWidth 3 p.t) ≤ S) (hcount : p.R+1 ≤ S)
    (hmetadata : ∀ x,SourceBank.MetadataBound (PackingMetadata.value P CollisionProgram.encodeType x) S)
    (hinc : ps.length ≤ S) :
    SourceReady.Input p ps P (Incidence.staged a) 0 n 0 S := by
  have hc := Incidence.staged_copy a h.destinations_empty
  have hex := staged_external a
  have hclean : ∀ i : Fin 340,i∉SourceReady.physicalLive →
      (Incidence.staged a).stacks (SourceReady.localPort i)=[] := by
    intro i hi
    have h550 : SourceReady.localPort i≠550 := by
      intro he
      have hv : i=210 := Fin.ext (by have := congrArg Fin.val he; dsimp [SourceReady.localPort] at this; omega)
      exact hi (by simp [hv,SourceReady.physicalLive])
    have hdest : ∀ z∈Incidence.pairs,SourceReady.localPort i≠z.2 := by
      intro z hz he
      have hv := congrArg Fin.val he
      simp only [Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals dsimp [SourceReady.localPort] at hv
      all_goals apply hi; simp only [SourceReady.physicalLive,List.mem_cons,List.mem_nil_iff,or_false]
      all_goals simp only [Fin.ext_iff,Fin.coe_ofNat_eq_mod]; omega
    rw [Incidence.staged_frame a _ h550 hdest]
    apply h.workerEmpty
    · dsimp [SourceReady.localPort]; omega
    · dsimp [SourceReady.localPort]; omega
    · intro he
      have hv : i=216 := Fin.ext (by have := congrArg Fin.val he; dsimp [SourceReady.localPort] at this; omega)
      exact hi (by simp [hv,SourceReady.physicalLive])
  have hfactor : (Incidence.staged a).stacks 556=[] := by
    rw [Incidence.staged_frame a 556 (by decide) (by
      intro z hz
      simp only [Incidence.pairs,List.mem_cons,List.mem_nil_iff,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)]
    exact hf
  refine ⟨h.staged.arithmetic,hclean,(hex 684 (Or.inr (by decide))).trans htmp,?_,?_,?_,hfactor,?_,
    ?_,?_,?_,?_,?_,?_,?_,hm.powerNegative,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    hsize,harray,hcount,hmetadata,hinc⟩
  · intro i hi
    have hg : 680 ≤ i.val := by
      simp only [SourceStaging.backupPorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl <;> decide
    exact (hex i (Or.inr hg)).trans (hback i hi)
  · exact Incidence.staged_cutoff a p.R h.radius (h.workerEmpty 550 (by decide) (by decide) (by decide))
  · exact (hc (128,552) (by decide)).trans h.ambientCount
  · exact h.staged_empty 573 (by decide)
  all_goals first
    | exact (hex _ (Or.inl (by decide))).trans hm.colors
    | exact (hex _ (Or.inl (by decide))).trans hm.nodes
    | exact (hex _ (Or.inl (by decide))).trans hm.typeWidth
    | exact (hex _ (Or.inr (by decide))).trans hm.positive
    | exact (hex _ (Or.inr (by decide))).trans hm.negative
    | exact (hex _ (Or.inl (by decide))).trans hm.scalarWidth
    | exact (hex _ (Or.inr (by decide))).trans hm.power
    | exact (hex _ (Or.inl (by decide))).trans hm.radius
    | exact (hex _ (Or.inl (by decide))).trans hm.offset
    | exact (hex _ (Or.inl (by decide))).trans hm.metadata
    | exact (hex _ (Or.inl (by decide))).trans hm.plans
    | exact (hex _ (Or.inr (by decide))).trans hm.inverses
    | exact (hex _ (Or.inr (by decide))).trans hm.negatives
    | exact (hex _ (Or.inr (by decide))).trans hm.differences
    | exact (hex _ (Or.inr (by decide))).trans hm.ringWidth
    | exact (hex _ (Or.inr (by decide))).trans hm.rowWidth
    | exact (hex _ (Or.inl (by decide))).trans hm.zero
    | exact (hex _ (Or.inl (by decide))).trans hm.one
    | exact (hex _ (Or.inl (by decide))).trans hm.minusOne
    | exact (hex _ (Or.inr (by decide))).trans hm.inverseDenominator

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
