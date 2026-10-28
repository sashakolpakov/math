import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramConcreteFinal
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramRepresentativeSemantics

namespace OAI.Algorithms

/-! The baseline is the physically folded first assignment of each attained
bucket. The choices below name those stored assignments, not extra input. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete
open MomentsAssembly

variable {n r D : ℕ} {H : Finset (Fin n)}
  {head : {v : Fin n // v∉H} → Fin r} {C : ℕ → ℕ → ℤ}

theorem first_fiber {g : Fin r} {table : HeadTable}
    (s : HeadSemantics H head g D C table)
    (y : {key : List Bool // key∈Finset.univ.image s.label}) :
    ∃ a : {a : Moments.Head head g → Bool // s.label a=y.val},
      (s.input y).assignments.headD []=s.encode a.val := by
  obtain ⟨xs,_,hc,he⟩ := s.fiber_enum y
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp y.property
  have hm := hc ⟨a,ha⟩
  cases xs with
  | nil => simp at hm
  | cons x xs => exact ⟨x,by rw [←he]; rfl⟩

def firstAssignment {g : Fin r} {table : HeadTable}
    (s : HeadSemantics H head g D C table)
    (y : {key : List Bool // key∈Finset.univ.image s.label}) :
    {a : Moments.Head head g → Bool // s.label a=y.val} :=
  (first_fiber s y).choose

theorem firstAssignment_word {g : Fin r} {table : HeadTable}
    (s : HeadSemantics H head g D C table)
    (y : {key : List Bool // key∈Finset.univ.image s.label}) :
    (s.input y).assignments.headD []=ambientEncode H head g (firstAssignment s y).val := by
  rw [(first_fiber s y).choose_spec,s.encode_eq]
  rfl

def headMask (H : Finset (Fin n)) (head : {v : Fin n // v∉H} → Fin r)
    (g : Fin r) (v : Fin n) : Bool :=
  if hv : v∉H then decide (head ⟨v,hv⟩=g) else false

def assembledValue (H : Finset (Fin n)) (head : {v : Fin n // v∉H} → Fin r)
    (a : ∀ g,Moments.Head head g → Bool) (v : Fin n) : Bool :=
  if hv : v∉H then a (head ⟨v,hv⟩) ⟨⟨v,hv⟩,rfl⟩ else false

theorem representative_indexed {G : Type*} (gs : List G) (input : G → HeadInput)
    (mask value : G → Fin n → Bool) (base : Fin n → Bool)
    (hm : ∀ g∈gs,(input g).mask=List.ofFn (mask g))
    (hv : ∀ g∈gs,(input g).assignments.headD []=List.ofFn (value g)) :
    Representative.representative (gs.map input) (List.ofFn base)=
      List.ofFn (Representative.assembled gs mask value base) := by
  induction gs generalizing base with
  | nil => rfl
  | cons g gs ih =>
      change Representative.representative (gs.map input)
        (LeafAssignmentMergeProgram.merge ((input g).assignments.headD []) (input g).mask
          (List.ofFn base)) = _
      rw [hv g (by simp),hm g (by simp),LeafAssignmentMergeProgram.merge_ofFn]
      exact ih _ (fun g hg=>hm g (by simp [hg])) (fun g hg=>hv g (by simp [hg]))

theorem assembled_heads (a : ∀ g,Moments.Head head g → Bool) :
    Representative.assembled (List.finRange r) (headMask H head)
      (fun g v=>if hv : v∉H then
        if hg : head ⟨v,hv⟩=g then a g ⟨⟨v,hv⟩,hg⟩ else false else false)
      (fun _=>false)=assembledValue H head a := by
  funext v
  by_cases hv : v∉H
  · apply Representative.assembled_hit
    · intro g hg hmask
      have hvg : head ⟨v,hv⟩=g := by simpa [headMask,hv] using hmask
      subst g
      simp [assembledValue,hv]
    · exact ⟨head ⟨v,hv⟩,by simp,by simp [headMask,hv]⟩
  · simpa [assembledValue,hv] using Representative.assembled_outside
      (List.finRange r) (headMask H head) _ (fun _=>false) v
      (fun g hg=>by simp [headMask,hv])

variable {tables : Fin r → HeadTable}
  (s : ∀ g,HeadSemantics H head g D C (tables g))
  (y : ∀ g,Moments.LabelValue (fun g=>(s g).label) g)

def baselineValue : Fin n → Bool :=
  assembledValue H head (fun g=>(firstAssignment (s g) (y g)).val)

theorem family_context
    (hm : ∀ g,(tables g).mask=List.ofFn (headMask H head g)) :
    (familyInput s y).context=List.ofFn (baselineValue s y) := by
  change Representative.representative
    (List.ofFn (fun g=>(s g).input (y g))) (List.replicate n false)=_
  rw [List.ofFn_eq_map,←List.ofFn_const]
  rw [representative_indexed (List.finRange r) (fun g=>(s g).input (y g))
    (headMask H head)
    (fun g v=>if hv : v∉H then
      if hg : head ⟨v,hv⟩=g then (firstAssignment (s g) (y g)).val ⟨⟨v,hv⟩,hg⟩
        else false else false)
    (fun _=>false)
    (fun g _=>((s g).input_mask (y g)).trans (hm g))
    (fun g hg=>firstAssignment_word (s g) (y g))]
  rw [assembled_heads]
  rfl

theorem baselineValue_head (g : Fin r) (v : Moments.Head head g) :
    baselineValue s y v.val.val=(firstAssignment (s g) (y g)).val v := by
  simp only [baselineValue,assembledValue,dite_eq_left v.val.property]
  rcases v with ⟨⟨v,hv⟩,hg⟩
  dsimp at hg ⊢
  subst g
  rfl

theorem baseline_label (g : Fin r) :
    (s g).label (fun v=>baselineValue s y v.val.val)=(y g).val := by
  have he : (fun v : Moments.Head head g=>baselineValue s y v.val.val)=
      (firstAssignment (s g) (y g)).val := by
    funext v
    exact baselineValue_head s y g v
  rw [he]
  exact (firstAssignment (s g) (y g)).property

theorem context_label
    (hm : ∀ g,(tables g).mask=List.ofFn (headMask H head g)) (g : Fin r) :
    (s g).label (fun v=>(familyInput s y).context.getD v.val.val.val false)=(y g).val := by
  rw [family_context s y hm]
  have he (v : Moments.Head head g) :
      (List.ofFn (baselineValue s y)).getD v.val.val.val false=baselineValue s y v.val.val := by
    simp [List.getD_eq_getElem?_getD,v.val.val.isLt]
  simp_rw [he]
  exact baseline_label s y g

end SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

end

end OAI.Algorithms
