import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcreteSourceJet
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteMerge
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramAssignmentConcrete

namespace OAI.Algorithms

/-! Actual attained bucket labels imply source-row baseline equality after
merging an owned-head assignment into the stored representative. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram PerturbationAssembly MomentsAssembly
open BucketTupleProgram.Concrete

variable {r Q d n : ℕ}

def freeHeadInclusion (H : Finset (Fin n)) (head : Fin n → Fin r) (g : Fin r) :
    Moments.Head (fun v : ResidualEmbedding.Free H=>head v.val) g ↪ Moments.Head head g :=
  ⟨fun v=>⟨v.val.val,v.property⟩,by intro a b h; apply Subtype.ext; apply Subtype.ext; exact congrArg (fun v : Moments.Head head g=>v.val) h⟩

theorem sum_head_free (H : Finset (Fin n)) (head : Fin n → Fin r) (g : Fin r)
    (C : Fin n → ℤ) (x : Fin n → Bool) (hx : ∀ v∈H,x v=false) :
    (∑ v : Moments.Head head g,C v.val*boolInt (x v.val)) =
      ∑ v : Moments.Head (fun v : ResidualEmbedding.Free H=>head v.val) g,
        C v.val.val*boolInt (x v.val.val) := by
  let e := freeHeadInclusion H head g
  calc
    _ = ∑ v∈(Finset.univ.map e),C v.val*boolInt (x v.val) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v hv hn
      have hH : v.val∈H := by
        by_contra h
        exact hn (Finset.mem_map.mpr ⟨⟨⟨v.val,h⟩,v.property⟩,Finset.mem_univ _,rfl⟩)
      simp [hx v.val hH,boolInt]
    _ = _ := by rw [Finset.sum_map]; rfl

theorem assemble_head {V G : Type*} (head : V → G)
    (a : ∀ g,Moments.Head head g → Bool) (g : G) (v : Moments.Head head g) :
    Moments.assemble head a v.val=a g v := by
  rcases v with ⟨v,hv⟩
  subst g
  rfl

theorem merged_signatures (H : Finset (Fin n)) (head : Fin n → Fin r)
    {D : ℕ} {C : ℕ → ℕ → ℤ} {tables : Fin r → BucketTupleProgram.HeadTable}
    (s : ∀ g,HeadSemantics H (fun v=>head v.val) g D C (tables g))
    (y : ∀ g,Moments.LabelValue (fun g=>(s g).label) g)
    (a : ∀ g,Moments.LabelBucket (fun g=>(s g).label) g (y g))
    (g k : Fin r) (hkg : k≠g) :
    LayoutExactBuckets.signature (fun (j : Fin D) (v : Moments.Head head k)=>C j.val v.val.val)
      (fun v=>boolInt (mergedValue s y g (a g).val v.val)) =
    LayoutExactBuckets.signature (fun (j : Fin D) (v : Moments.Head head k)=>C j.val v.val.val)
      (fun v=>boolInt (HighIncidence.glue H (fun _=>false)
        (Moments.assemble (fun v=>head v.val) (fun k=>(a k).val)) v.val)) := by
  funext j
  change (∑ v : Moments.Head head k,C j.val v.val.val*boolInt (mergedValue s y g (a g).val v.val)) =
    ∑ v : Moments.Head head k,C j.val v.val.val*boolInt (HighIncidence.glue H (fun _=>false)
      (Moments.assemble (fun v=>head v.val) (fun k=>(a k).val)) v.val)
  rw [sum_head_free H head k (fun v=>C j.val v.val) _ (merged_high s y g (a g).val)]
  rw [sum_head_free H head k (fun v=>C j.val v.val)
    (HighIncidence.glue H (fun _=>false) (Moments.assemble (fun v=>head v.val) (fun k=>(a k).val)))
    (by intro v hv; simp [HighIncidence.glue,hv])]
  have he := ((s k).kernel
    (fun v=>mergedValue s y g (a g).val v.val.val) (a k).val).mp
    ((merged_foreign_label s y g k hkg (a g).val).trans (a k).property.symm) j
  have ha (v : Moments.Head (fun v : ResidualEmbedding.Free H=>head v.val) k) :
      HighIncidence.glue H (fun _=>false)
        (Moments.assemble (fun v=>head v.val) (fun k=>(a k).val)) v.val.val=(a k).val v := by
    simp only [HighIncidence.glue,dite_eq_right v.val.property]
    exact assemble_head _ (fun k=>(a k).val) k v
  simp_rw [ha]
  simpa only [boolInt] using he

theorem merged_owned_ambient (H : Finset (Fin n)) (head : Fin n → Fin r)
    {D : ℕ} {C : ℕ → ℕ → ℤ} {tables : Fin r → BucketTupleProgram.HeadTable}
    (s : ∀ g,HeadSemantics H (fun v=>head v.val) g D C (tables g))
    (y : ∀ g,Moments.LabelValue (fun g=>(s g).label) g)
    (a : ∀ g,Moments.LabelBucket (fun g=>(s g).label) g (y g))
    (g : Fin r) (v : Fin n) (hv : head v=g) :
    mergedValue s y g (a g).val v =
      HighIncidence.glue H (fun _=>false)
        (Moments.assemble (fun v=>head v.val) (fun k=>(a k).val)) v := by
  by_cases hH : v∈H
  · simp only [merged_high s y g (a g).val v hH,HighIncidence.glue,dite_eq_left hH]
  · rw [show mergedValue s y g (a g).val v=(a g).val ⟨⟨v,hH⟩,hv⟩ from
      merged_owned s y g (a g).val ⟨⟨v,hH⟩,hv⟩]
    simp only [HighIncidence.glue,dite_eq_right hH]
    exact (assemble_head _ (fun k=>(a k).val) g ⟨⟨v,hH⟩,hv⟩).symm

theorem merged_baseline_eq (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (howner : ∀ i,(ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r) (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (H : Finset (Fin n)) (t : Fin Q)
    {tables : Fin r → BucketTupleProgram.HeadTable}
    (s : ∀ g,HeadSemantics H (fun v=>head t v.val) g ps.length
      (LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t) (tables g))
    (y : ∀ g,Moments.LabelValue (fun g=>(s g).label) g)
    (a : ∀ g,Moments.LabelBucket (fun g=>(s g).label) g (y g))
    (hm : ∀ g,(tables g).mask=List.ofFn (headMask H (fun v=>head t v.val) g))
    (theta : DensePolynomialProgram.Coeff (SubexponentialSAT.SubexpLiftRing.baseWidth 3 p.t) d)
    (htheta : p.ops.decode theta=p.model.node p.t Q p.ht p.hfield t)
    (high bits : List Bool) (support : List Bool)
    (f j : ℕ) (hj : (j,n+f)∈ps)
    (hzero : ∀ v∈H,fixedSourceRow p ps P n f j v=0)
    (g : Fin r) (hg : (P.label (planIndex ps n f j hj)).slot 0 t=g) :
    baseline (n:=n) p ps P theta
      (FactorLoop.assignmentReference high bits
        ⟨support,((s g).input (y g)).mask,((s g).input (y g)).context,(familyInput s y).context⟩
        ((s g).encode (a g).val)) f j =
      ∑ v : ResidualEmbedding.Free H,(fixedSourceRow p ps P n f j v.val).eval (p.ops.decode theta)*
        HashInput.boolValue (Moments.assemble (fun v=>head t v.val) (fun k=>(a k).val) v) := by
  let state := FactorLoop.assignmentReference high bits
    ⟨support,((s g).input (y g)).mask,((s g).input (y g)).context,(familyInput s y).context⟩
    ((s g).encode (a g).val)
  have hs145 : state 145=List.ofFn (mergedValue s y g (a g).val) := by
    change (FactorLoop.assignmentReference high bits _ _) 145=_
    simp only [FactorLoop.assignmentReference,Function.update_of_ne (by decide : (145:Fin 768)≠703),
      Function.update_of_ne (by decide : (145:Fin 768)≠702),Function.update_same]
    exact merged_word s y hm g (a g).val
  have hv (v : Fin n) : (state 145).getD v.val false=mergedValue s y g (a g).val v := by
    rw [hs145]
    simp [List.getD_eq_getElem?_getD,v.isLt]
  apply baseline_eq_free p ps P owner howner head hhead H (fun _=>false) _ theta state
    f j hj t htheta hzero
  · intro v hh
    rw [hv]
    exact merged_owned_ambient H (head t) s y a g v (hh.trans hg)
  · intro k hk
    simp only [hv]
    exact merged_signatures H (head t) s y a g k (by simpa only [hg] using hk)

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
