import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBankFrameReady
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramPackLabels

namespace OAI.Algorithms

/-! Cache and workspace invariants for the actual metadata dispatch. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
attribute [local simp] Fin.coe_ofNat_eq_mod

/-- The metadata return fields may be populated, while all disposable source
workspace is empty. Arithmetic services keep their separate native caches. -/
structure WorkReady (a : Data) : Prop where
  work : ∀ j∈cleanupPorts, (j.val < 288 ∨ 293 < j.val) → a.stacks j=[]
  temp : a.stacks 319=[]
  output : a.stacks 287=[]
  count : a.stacks 37=[]
  tableCount : a.stacks 64=[]
  tableAccum : a.stacks 65=[]
  low : ∀ j : Fin 320,j.val < 4 → a.stacks j=[]

theorem metadata_frame (a : Data) (mr mc : GlobalBasisMetadata.Metadata)
    (j : Fin 320) (hj : j.val < 288 ∨ 293 < j.val) :
    metadataStacks a mr mc j=a.stacks j := by
  have h288 : j≠288 := by intro h; subst j; norm_num at hj
  have h289 : j≠289 := by intro h; subst j; norm_num at hj
  have h290 : j≠290 := by intro h; subst j; norm_num at hj
  have h291 : j≠291 := by intro h; subst j; norm_num at hj
  have h292 : j≠292 := by intro h; subst j; norm_num at hj
  have h293 : j≠293 := by intro h; subst j; norm_num at hj
  simp [metadataStacks,h288,h289,h290,h291,h292,h293]

theorem WorkReady.metadata {a b : Data} (h : WorkReady a)
    (mr mc : GlobalBasisMetadata.Metadata) (hb : b.stacks=metadataStacks a mr mc) : WorkReady b := by
  constructor
  · intro j hj hk; rw [hb,metadata_frame a mr mc j hk]; exact h.work j hj hk
  · rw [hb,metadata_frame a mr mc 319 (Or.inr (by decide))]; exact h.temp
  · rw [hb,metadata_frame a mr mc 287 (Or.inl (by decide))]; exact h.output
  · rw [hb,metadata_frame a mr mc 37 (Or.inl (by decide))]; exact h.count
  · rw [hb,metadata_frame a mr mc 64 (Or.inl (by decide))]; exact h.tableCount
  · rw [hb,metadata_frame a mr mc 65 (Or.inl (by decide))]; exact h.tableAccum
  · intro j hj; rw [hb,metadata_frame a mr mc j (Or.inl (by omega))]; exact h.low j hj

theorem WorkReady.frame {a b : Data} (h : WorkReady a) (hb : b.stacks=a.stacks) : WorkReady b := by
  constructor
  · intro j hj hk; rw [hb]; exact h.work j hj hk
  · rw [hb]; exact h.temp
  · rw [hb]; exact h.output
  · rw [hb]; exact h.count
  · rw [hb]; exact h.tableCount
  · rw [hb]; exact h.tableAccum
  · intro j hj; rw [hb]; exact h.low j hj

theorem WorkReady.literal {a : Data} (h : WorkReady a) :
    a.stacks 319=[] ∧ a.stacks 315=[] ∧ a.stacks 316=[] ∧ a.stacks 287=[] := by
  exact ⟨h.temp,h.work 315 (by decide) (Or.inr (by decide)),
    h.work 316 (by decide) (Or.inr (by decide)),h.output⟩

theorem WorkReady.compare {a : Data} (h : WorkReady a) :
    a.stacks 301=[] ∧ a.stacks 302=[] ∧ a.stacks 303=[] ∧ a.stacks 307=[] := by
  exact ⟨h.work 301 (by decide) (Or.inr (by decide)),
    h.work 302 (by decide) (Or.inr (by decide)),
    h.work 303 (by decide) (Or.inr (by decide)),
    h.work 307 (by decide) (Or.inr (by decide))⟩

theorem WorkReady.emitter {a : Data} (h : WorkReady a) : EmitterClean a := by
  intro j hj hk hn
  by_cases h287 : j=287
  · subst j; exact h.output
  have hm : j∈cleanupPorts := by
    have hr : j∈List.ofFn (fun i : Fin 31 => (⟨256+i.val,by omega⟩ : Fin 320)) := by
      apply List.mem_ofFn.mpr
      refine ⟨⟨j.val-256,by omega⟩,?_⟩
      apply Fin.ext; simp; omega
    simp only [cleanupPorts,List.mem_append]
    exact Or.inl (Or.inl (Or.inr hr))
  exact h.work j hm (Or.inl (by omega))

theorem cleared_metadata (a : Data) (mr mc : GlobalBasisMetadata.Metadata)
    (rf : Fin 16 → Bool) :
    clearedStacks (⟨rf,metadataStacks a mr mc⟩ : Data)=clearedStacks a := by
  funext j
  simp only [clearedStacks]
  by_cases hj : j∈cleanupPorts
  · simp [hj]
  · simp only [ite_eq_right hj]
    apply metadata_frame
    by_contra hn
    have hr : 288 ≤ j.val ∧ j.val ≤ 293 := by omega
    have hm : j∈List.ofFn (fun i : Fin 16 => (⟨288+i.val,by omega⟩ : Fin 320)) := by
      apply List.mem_ofFn.mpr
      refine ⟨⟨j.val-288,by omega⟩,?_⟩
      apply Fin.ext; simp; omega
    apply hj
    simp only [cleanupPorts,List.mem_append]
    exact Or.inl (Or.inr hm)

theorem cleared_eq {a : Data} (h : ∀ j∈cleanupPorts,a.stacks j=[]) : clearedStacks a=a.stacks := by
  funext j
  simp only [clearedStacks]
  split_ifs with hj
  · exact (h j hj).symm
  · rfl

def MetadataBound (m : GlobalBasisMetadata.Metadata) (S : ℕ) : Prop :=
  m.block.length ≤ S ∧ m.typeCode.length ≤ S ∧ m.rank.length ≤ S

theorem metadata_length {a b : Data} (mr mc : GlobalBasisMetadata.Metadata) (S : ℕ)
    (hb : b.stacks=metadataStacks a mr mc) (ha : ∀ j,(a.stacks j).length ≤ S)
    (hr : MetadataBound mr S) (hc : MetadataBound mc S) :
    ∀ j,(b.stacks j).length ≤ S := by
  intro j
  rw [hb]
  simp only [metadataStacks,Function.update_apply]
  split_ifs <;> first
    | exact hr.1
    | exact hr.2.1
    | exact hr.2.2
    | exact hc.1
    | exact hc.2.1
    | exact hc.2.2
    | exact ha j

theorem lookup_ready {a : Data} (h : ∀ j∈cleanupPorts,a.stacks j=[]) :
    ∀ j : Fin 320,288 ≤ j.val → j.val ≤ 300 → a.stacks j=[] := by
  intro j hj hk
  apply h
  have hm : j∈List.ofFn (fun i : Fin 16 => (⟨288+i.val,by omega⟩ : Fin 320)) := by
    apply List.mem_ofFn.mpr
    refine ⟨⟨j.val-288,by omega⟩,?_⟩
    apply Fin.ext; simp; omega
  simp only [cleanupPorts,List.mem_append]
  exact Or.inl (Or.inr hm)

theorem cleared_metadata_eq {a b : Data} (mr mc : GlobalBasisMetadata.Metadata)
    (h : ∀ j∈cleanupPorts,a.stacks j=[]) (hb : b.stacks=metadataStacks a mr mc) :
    clearedStacks b=a.stacks := by
  have hh := cleared_metadata a mr mc b.regs
  have he : b=(⟨b.regs,metadataStacks a mr mc⟩ : Data) :=
    SubexpScanPrimitives.state_ext rfl hb
  rw [he,hh,cleared_eq h]

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
