import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramMembership
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgramSource
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramControllerSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgramPartition
import OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsBuckets

namespace OAI.Algorithms

/-! Finite reindexing of the exact stored records. The witnesses below only
name already stored values; no additional runtime enumeration is assumed. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

open BucketProgram

theorem finite_reindex {A B : Type*} (encode : A → B) (ws : List B)
    (hinj : Function.Injective encode) (hn : ws.Nodup)
    (hm : ∀ w,w∈ws ↔ ∃ a,encode a=w) :
    ∃ xs : List A,xs.Nodup ∧ (∀ a,a∈xs) ∧ xs.map encode=ws := by
  classical
  let decode (w : {w // w∈ws}) : A := Classical.choose ((hm w.val).mp w.property)
  have hd (w : {w // w∈ws}) : encode (decode w)=w.val :=
    Classical.choose_spec ((hm w.val).mp w.property)
  let xs := ws.attach.map decode
  have he : xs.map encode=ws := by
    change (ws.attach.map decode).map encode=ws
    rw [List.map_map]
    simpa only [List.attach_map_subtype_val] using
      (List.map_congr_left (fun w _=>hd w) :
        ws.attach.map (encode ∘ decode)=ws.attach.map Subtype.val)
  refine ⟨xs,?_,?_,he⟩
  · exact List.Nodup.of_map encode (he.symm ▸ hn)
  · intro a
    have ha : encode a∈xs.map encode := by rw [he]; exact (hm _).mpr ⟨a,rfl⟩
    obtain ⟨b,hb,hab⟩ := List.mem_map.mp ha
    exact hinj hab ▸ hb

theorem full_toFinset {A : Type*} [Fintype A] [DecidableEq A]
    (xs : List A) (hx : ∀ a,a∈xs) : xs.toFinset=Finset.univ := by
  ext a
  simp [hx a]

structure RecordModel (A : Type*) (records : List Record) where
  label : A → List Bool
  encode : A → List Bool
  encode_injective : Function.Injective encode
  payloads_nodup : (records.map Prod.snd).Nodup
  mem_iff : ∀ key word,(key,word)∈records ↔ ∃ a,label a=key ∧ encode a=word

namespace RecordModel

variable {A : Type*} [Fintype A] {records : List Record} (m : RecordModel A records)

abbrev Attained := {key : List Bool // key∈Finset.univ.image m.label}
abbrev Fiber (y : m.Attained) := {a : A // m.label a=y.val}

theorem attained_iff_keys (key : List Bool) :
    key∈Finset.univ.image m.label ↔ key∈Controller.keys records := by
  classical
  rw [Controller.mem_keys]
  constructor
  · rintro hk
    obtain ⟨a,_,ha⟩ := Finset.mem_image.mp hk
    exact ⟨m.encode a,(m.mem_iff _ _).mpr ⟨a,ha,rfl⟩⟩
  · rintro ⟨word,hw⟩
    obtain ⟨a,ha,_⟩ := (m.mem_iff _ _).mp hw
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,ha⟩

def inputHead (mask context : List Bool) (y : m.Attained) : MomentsAssembly.HeadInput :=
  ⟨mask,context,bucketAssignments records y.val⟩

theorem fiber_enumeration (mask context : List Bool) (y : m.Attained) :
    ∃ xs : List (m.Fiber y),xs.Nodup ∧ (∀ a,a∈xs) ∧
      xs.map (fun a=>m.encode a.val)=(m.inputHead mask context y).assignments := by
  apply finite_reindex (fun a : m.Fiber y=>m.encode a.val)
  · intro a b hab
    exact Subtype.ext (m.encode_injective hab)
  · exact bucketAssignments_nodup records y.val m.payloads_nodup
  · intro word
    change word∈bucketAssignments records y.val ↔ _
    rw [mem_bucketAssignments,m.mem_iff]
    constructor
    · rintro ⟨a,ha,he⟩
      exact ⟨⟨a,ha⟩,he⟩
    · rintro ⟨a,he⟩
      exact ⟨a.val,a.property,he⟩

theorem inputHead_injective (mask context : List Bool) :
    Function.Injective (m.inputHead mask context) := by
  classical
  intro x y hxy
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp x.property
  have hm : m.encode a∈bucketAssignments records x.val :=
    (mem_bucketAssignments _ _ _).mpr ((m.mem_iff _ _).mpr ⟨a,ha,rfl⟩)
  have he : bucketAssignments records x.val=bucketAssignments records y.val :=
    congrArg MomentsAssembly.HeadInput.assignments hxy
  rw [he] at hm
  obtain ⟨b,hb,hab⟩ := (m.mem_iff _ _).mp ((mem_bucketAssignments _ _ _).mp hm)
  have hba := m.encode_injective hab
  subst b
  exact Subtype.ext (ha.symm.trans hb)

def modelTable (mask context : List Bool) : HeadTable :=
  ⟨mask,context,controllerBuckets records⟩

theorem model_choices (mask context : List Bool) :
    (modelTable (records:=records) mask context).choices=
      ((Controller.keys records).map (fun key=>
        (⟨mask,context,bucketAssignments records key⟩ : MomentsAssembly.HeadInput))).reverse := by
  simp [modelTable,HeadTable.choices,controllerBuckets,List.map_map,Function.comp_def]

theorem model_choices_mem (mask context : List Bool) (h : MomentsAssembly.HeadInput) :
    h∈(modelTable (records:=records) mask context).choices ↔
      ∃ y : m.Attained,m.inputHead mask context y=h := by
  rw [model_choices,List.mem_reverse,List.mem_map]
  constructor
  · rintro ⟨key,hkey,he⟩
    exact ⟨⟨key,(m.attained_iff_keys key).mpr hkey⟩,he⟩
  · rintro ⟨y,he⟩
    exact ⟨y.val,(m.attained_iff_keys y.val).mp y.property,he⟩

include m in
theorem model_choices_nodup (mask context : List Bool) :
    (modelTable (records:=records) mask context).choices.Nodup := by
  rw [model_choices,List.nodup_reverse]
  apply (Controller.keys_nodup records).map_on
  intro x hx y hy he
  have h := m.inputHead_injective mask context
    (a₁:=⟨x,(m.attained_iff_keys x).mpr hx⟩)
    (a₂:=⟨y,(m.attained_iff_keys y).mpr hy⟩) he
  exact congrArg Subtype.val h

theorem label_enumeration (mask context : List Bool) :
    ∃ ys : List m.Attained,ys.Nodup ∧ (∀ y,y∈ys) ∧
      ys.map (m.inputHead mask context)=(modelTable (records:=records) mask context).choices :=
  finite_reindex _ _ (m.inputHead_injective mask context)
    (m.model_choices_nodup mask context) (m.model_choices_mem mask context)

end RecordModel
end SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

end

end OAI.Algorithms
