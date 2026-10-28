import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteProduced

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete
open BucketProgram MomentsAssembly
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking

theorem ofFn_tableAt {r : ℕ} (tables : List HeadTable) (hlen : tables.length=r) :
    List.ofFn (fun g : Fin r=>tables.get (Fin.cast hlen.symm g))=tables := by
  subst r
  simpa only [Fin.cast_refl,id_eq,List.get_eq_getElem] using (List.ofFn_getElem :
    List.ofFn (fun i : Fin tables.length => tables[i.val]) = tables)

def FinalizedMeaning {n r : ℕ} (H : Finset (Fin n))
    (head : {v : Fin n // v∉H} → Fin r) (D : ℕ) (C : ℕ → ℕ → ℤ)
    (tables : List HeadTable) (hlen : tables.length=r) : Prop :=
  ∃ s : ∀ g : Fin r,HeadSemantics H head g D C (tables.get (Fin.cast hlen.symm g)),
    ∃ ys : List (∀ g,Moments.LabelValue (fun g=>(s g).label) g),
      ys.Nodup ∧ ys.toFinset=Finset.univ ∧ ys.map (familyInput s)=
        ((enumerate tables).map (Representative.bucket n)).reverse

theorem producedHeads_finalized {n r N D B z : ℕ} {base : LeafHeadSetupProgram.Data}
    {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {tables : List HeadTable}
    (H : Finset (Fin n)) (head : {v : Fin n // v∉H} → Fin r)
    (hp : LeafHeadSetupProgram.ProducedHeads base n N D rows low Rel B z tables)
    (hlen : tables.length=r)
    (hs : ∀ g : Fin r,∀ v : Fin n,v.val∈LeafHeadSetupProgram.selectedHeads n rows low (z+g.val) ↔
      ∃ hv : v∉H,head ⟨v,hv⟩=g)
    (C : ℕ → ℕ → ℤ)
    (hrel : ∀ j v p,j < D→v < n→Rel j v p→
      SubexponentialSAT.BinaryArithmetic.toNat p.2 ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141) ∧
      (SubexponentialSAT.BinaryArithmetic.toNat p.1 : ℤ)-(SubexponentialSAT.BinaryArithmetic.toNat p.2 : ℤ)=C j v) :
    FinalizedMeaning H head D C tables hlen := by
  obtain ⟨s⟩ := producedHeads_semantics H head hp hlen hs C hrel
  obtain ⟨ys,hn,hc,he⟩ := family_enumeration s
  rw [ofFn_tableAt tables hlen] at he
  exact ⟨s,ys,hn,hc,he⟩

theorem producedHeads_literal_finalized {n r Q N D B z : ℕ} {base : LeafHeadSetupProgram.Data}
    {rows : List (List Bool)} {low : List Bool} {tables : List HeadTable}
    (Hfree : Finset (Fin n)) (head : {v : Fin n // v∉Hfree} → Fin r)
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R : ℕ) (t : Fin Q)
    (ps : Fin D → ℕ × ℕ) (hps : ∀ i,(ps i).1=(owner i).val) (mass : ℕ)
    (hp : LeafHeadSetupProgram.ProducedHeads base n N D rows low
      (ProducedRank.FiberRel (List.ofFn ps) (ProducedRank.entryNat P A R t) mass) B z tables)
    (hlen : tables.length=r)
    (hs : ∀ g : Fin r,∀ v : Fin n,v.val∈LeafHeadSetupProgram.selectedHeads n rows low (z+g.val) ↔
      ∃ hv : v∉Hfree,head ⟨v,hv⟩=g)
    (hW : mass ≤ SubexponentialSAT.BinaryArithmetic.toNat (base.stacks 141)) :
    FinalizedMeaning Hfree head D (LayoutProducedMatrix.literalNat P owner A R t) tables hlen := by
  apply producedHeads_finalized Hfree head hp hlen hs
  intro j v p hj hv hr
  have he := ProducedRank.fiberRel_realizes P owner A R t ps hps mass j v p hj hv hr
  refine ⟨?_,he.1⟩
  have hm := hr.2
  unfold RowSelectionProgram.pairTotal at hm
  omega

variable {I : Type*} [Fintype I] [DecidableEq I] {n N r Q : ℕ}

def sourceFreeHead (owner : I → Fin n) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin n) Q))
    (x y : ℚ) (H : Finset (Fin n)) (t : Fin Q) : {v : Fin n // v∉H} → Fin r :=
  fun v=>Packing.computedWords owner factor a tail terms
    (LeafHeadFactorsProgram.indices n N) x y (.inl v.val) t

omit [DecidableEq I] in
/-- The selection premise of producedHeads_literal_finalized follows from
the actual source-row semantics at this node; it is not an abstract partition. -/
theorem source_ids_spec (owner : I → Fin n) (factor : I → Fin N)
    (a : Word r Q) (tail : List (Word r Q))
    (terms : List (Packing.ScoreTerm I (Fin n) Q)) (w : PackingProgram.Weights)
    (x y : ℚ) (hy : y^2=(w.incidence:ℚ)/w.denominator)
    (hx : x^2=(w.head:ℚ)/w.denominator) (H : Finset (Fin n))
    (t : Fin Q) (g : Fin r) (v : Fin n) :
    v.val∈LeafHeadSetupProgram.selectedHeads n
      (LeafHeadFactorsProgram.sourceRows owner factor a tail terms w)
      (HeadIdentifierProgram.lowBits (fun v=>decide (v∉H))) (t.val*r+g.val) ↔
      ∃ hv : v∉H,sourceFreeHead owner factor a tail terms x y H t ⟨v,hv⟩=g := by
  rw [LeafHeadSetupProgram.selectedHeads_source_mem owner factor a tail terms w x y hy hx]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨hv,hg⟩
    exact ⟨hv,hg⟩
  · rintro ⟨hv,hg⟩
    exact ⟨hv,hg⟩

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

end

end OAI.Algorithms
