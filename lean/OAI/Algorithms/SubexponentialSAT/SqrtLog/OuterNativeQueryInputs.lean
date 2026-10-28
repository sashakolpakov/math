import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeStage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativeMassFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryInputConstruct

namespace OAI.Algorithms

/-! Input facts for each actual marked-reference callback. The collector's
arbitrary queue and accumulator are not part of the reusable query workspace. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls LeafProgram
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev markedStart (base : Query.Data) (tail bits : List Bool) : Query.Data :=
  RecordPrograms.state Marked.Wide.recordPorts base false true false tail bits.reverse

theorem workspace_eq_at {a b : Query.Data}
    (h : Marked.Wide.workspace a=Marked.Wide.workspace b) (i : Fin 768)
    (hi : i.val < 320 ∨ 324 < i.val) : a.stacks i=b.stacks i := by
  rcases hi with hi|hi
  · let j : Fin 763 := ⟨i.val,by omega⟩
    have hj : Marked.Wide.workPort j=i := by
      apply Fin.ext
      simp [Marked.Wide.workPort,j,hi]
    simpa only [Marked.Wide.workspace,hj] using congrFun h j
  · let j : Fin 763 := ⟨i.val-5,by have:=i.isLt; omega⟩
    have hj : Marked.Wide.workPort j=i := by
      apply Fin.ext
      have hn : ¬j.val < 320 := by dsimp [j]; omega
      simp only [Marked.Wide.workPort,hn]
      dsimp [j]
      omega
    simpa only [Marked.Wide.workspace,hj] using congrFun h j

theorem marked_start_workspace (base : Query.Data) (tail bits : List Bool) :
    Marked.Wide.workspace (markedStart base tail bits)=Marked.Wide.workspace base :=
  Marked.Wide.workspace_recordState base false true false tail bits.reverse

theorem marked_start_sources (q : LeafQueryFrontend.Query) (source base : Query.Data)
    (tail bits : List Bool) (hs : Query.Sources q source)
    (hw : Marked.Wide.workspace base=Marked.Wide.workspace source) :
    Query.Sources q (markedStart base tail bits) := by
  have h := (marked_start_workspace base tail bits).trans hw
  exact ⟨(workspace_eq_at h 700 (by decide)).trans hs.formula,
    (workspace_eq_at h 701 (by decide)).trans hs.rows,
    (workspace_eq_at h 707 (by decide)).trans hs.modulus,
    (workspace_eq_at h 708 (by decide)).trans hs.width,
    (workspace_eq_at h 709 (by decide)).trans hs.ambient⟩

theorem marked_start_clean (source base : Query.Data) (tail bits : List Bool)
    (hc : Query.CleanWork source)
    (hw : Marked.Wide.workspace base=Marked.Wide.workspace source)
    (h324 : base.stacks 324=[]) : Query.CleanWork (markedStart base tail bits) := by
  intro i hp h321
  by_cases h : i=324
  · subst i
    simpa [markedStart,RecordPrograms.state,Marked.Wide.recordPorts] using h324
  have h320 : i≠320 := by intro he; subst i; exact hp (by decide)
  have h322 : i≠322 := by intro he; subst i; exact hp (by decide)
  have h323 : i≠323 := by intro he; subst i; exact hp (by decide)
  have hi : i.val < 320 ∨ 324 < i.val := by
    have := Fin.val_ne_of_ne h320
    have := Fin.val_ne_of_ne h321
    have := Fin.val_ne_of_ne h322
    have := Fin.val_ne_of_ne h323
    have := Fin.val_ne_of_ne h
    norm_num at *
    omega
  exact (workspace_eq_at ((marked_start_workspace base tail bits).trans hw) i hi).trans
    (hc i hp h321)

theorem marked_start_high (source base : Query.Data) (tail bits : List Bool)
    (hh : ∀i : Fin 768,744 ≤ i.val → source.stacks i=[])
    (hw : Marked.Wide.workspace base=Marked.Wide.workspace source) :
    ∀i : Fin 768,744 ≤ i.val → (markedStart base tail bits).stacks i=[] := by
  intro i hi
  exact (workspace_eq_at ((marked_start_workspace base tail bits).trans hw) i
    (Or.inr (by omega))).trans (hh i hi)

theorem marked_start_zero (base : Query.Data) (tail bits : List Bool)
    (h : base.stacks 323=[]) : (markedStart base tail bits).stacks 323=[] := by
  simpa [markedStart,RecordPrograms.state,Marked.Wide.recordPorts] using h

@[simp] theorem marked_start_reference (base : Query.Data) (tail bits : List Bool) :
    (markedStart base tail bits).stacks 321=bits.reverse := by
  simp [markedStart,RecordPrograms.state,Marked.Wide.recordPorts]

theorem trial_high_empty (a : LeafOuterProgram.Data) (ha : LeafOuterProgram.WorkerEmpty a) :
    ∀i : Fin 768,744 ≤ i.val →
      (projectState id LeafOuterProgram.workerStack (LeafOuterNative.trialStaged a)).stacks i=[] := by
  intro i hi
  change (LeafOuterNative.trialStaged a).stacks (LeafOuterProgram.workerStack i)=[]
  rw [LeafOuterNative.trialStaged_frame]
  · exact ha i
  all_goals intro h; have hv:=congrArg Fin.val h; dsimp [LeafOuterProgram.workerStack] at hv; omega

end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
