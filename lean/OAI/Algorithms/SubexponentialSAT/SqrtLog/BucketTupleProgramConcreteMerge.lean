import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteBaseline

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete
open MomentsAssembly

variable {n r D : ℕ} {H : Finset (Fin n)}
  {head : {v : Fin n // v∉H} → Fin r} {C : ℕ → ℕ → ℤ}

theorem selectedMask_eq {rows : List (List Bool)} {low : List Bool} {z : ℕ}
    (g : Fin r)
    (hs : ∀ v : Fin n,v.val∈LeafHeadSetupProgram.selectedHeads n rows low z ↔
      ∃ hv : v∉H,head ⟨v,hv⟩=g) :
    LeafHeadSetupProgram.selectedMask n rows low z=List.ofFn (headMask H head g) := by
  change HeadScatterProgram.mask n
    (HeadIdentifierProgram.chosenIds (HeadIdentifierProgram.predicate rows low z) n)
    (List.replicate (HeadIdentifierProgram.count _ n) true)=_
  rw [HeadIdentifierProgram.support_mask_eq]
  congr 1
  funext v
  apply Bool.eq_iff_iff.mpr
  have he := hs v
  simp only [LeafHeadSetupProgram.selectedHeads,HeadIdentifierProgram.chosenIds,
    List.mem_filter,List.mem_range,v.isLt,true_and] at he
  by_cases hv : v∉H
  · simpa [headMask,hv] using he
  · simpa [headMask,hv] using he

theorem producedHeads_masks {N B z : ℕ} {base : LeafHeadSetupProgram.Data}
    {rows : List (List Bool)} {low : List Bool}
    {Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop} {tables : List HeadTable}
    (hp : LeafHeadSetupProgram.ProducedHeads base n N D rows low Rel B z tables)
    (hlen : tables.length=r)
    (hs : ∀ g : Fin r,∀ v : Fin n,v.val∈LeafHeadSetupProgram.selectedHeads n rows low (z+g.val) ↔
      ∃ hv : v∉H,head ⟨v,hv⟩=g) (g : Fin r) :
    (tables.get (Fin.cast hlen.symm g)).mask=List.ofFn (headMask H head g) := by
  obtain ⟨mr,ys,hr,hy,ht⟩ := producedHeads_get hp (Fin.cast hlen.symm g)
  rw [ht]
  exact selectedMask_eq g (hs g)

variable {tables : Fin r → HeadTable}
  (s : ∀ g,HeadSemantics H head g D C (tables g))
  (y : ∀ g,Moments.LabelValue (fun g=>(s g).label) g)

def mergedValue (g : Fin r) (a : Moments.Head head g → Bool) (v : Fin n) : Bool :=
  if headMask H head g v then
    (if hv : v∉H then if hg : head ⟨v,hv⟩=g then a ⟨⟨v,hv⟩,hg⟩ else false else false)
  else baselineValue s y v

theorem merged_word
    (hm : ∀ g,(tables g).mask=List.ofFn (headMask H head g))
    (g : Fin r) (a : Moments.Head head g → Bool) :
    LeafAssignmentMergeProgram.merge ((s g).encode a) ((s g).input (y g)).mask
      (familyInput s y).context=List.ofFn (mergedValue s y g a) := by
  rw [(s g).encode_eq,(s g).input_mask (y g),hm g,family_context s y hm]
  exact LeafAssignmentMergeProgram.merge_ofFn _ _ _

theorem merged_owned (g : Fin r) (a : Moments.Head head g → Bool)
    (v : Moments.Head head g) : mergedValue s y g a v.val.val=a v := by
  simp only [mergedValue, headMask, v.val.property, v.property]
  apply congrArg a
  exact Subtype.ext rfl

theorem merged_foreign (g k : Fin r) (hne : k≠g) (a : Moments.Head head g → Bool)
    (v : Moments.Head head k) :
    mergedValue s y g a v.val.val=baselineValue s y v.val.val := by
  simp [mergedValue,headMask,v.val.property,v.property,hne]

theorem merged_foreign_label (g k : Fin r) (hne : k≠g)
    (a : Moments.Head head g → Bool) :
    (s k).label (fun v=>mergedValue s y g a v.val.val)=(y k).val := by
  simp_rw [merged_foreign s y g k hne a]
  exact baseline_label s y k

theorem merged_owned_label (g : Fin r)
    (a : Moments.LabelBucket (fun g=>(s g).label) g (y g)) :
    (s g).label (fun v=>mergedValue s y g a.val v.val.val)=(y g).val := by
  simp_rw [merged_owned s y g a.val]
  exact a.property

theorem merged_high (g : Fin r) (a : Moments.Head head g → Bool)
    (v : Fin n) (hv : v∈H) : mergedValue s y g a v=false := by
  simp [mergedValue,headMask,baselineValue,assembledValue,hv]

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

end

end OAI.Algorithms
