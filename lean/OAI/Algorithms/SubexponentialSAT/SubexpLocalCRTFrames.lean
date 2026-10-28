import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLocalCRTSetup
import OAI.Algorithms.SubexponentialSAT.SubexpNodeScanControl

namespace OAI.Algorithms

/-! Finite workspace and cleanup lemmas for the local CRT program. These
are store equalities and actual clear-loop traces, with no arithmetic oracle. -/

namespace SubexponentialSAT.SubexpLocalCRTFrames

open BitProgram StructuredCalls SubexpConvolutionControl

def scratch : List (Fin 256) :=
  [100,101,102,103,105,106,107,108,109,110,120,121,122,
   205,208,209,210,215,217,218,219,220,221,222,223,224,226,227,228,229,
   240,241,242,245,246,247,248]

def command : Code := SubexpLocalCRTSetup.clearMany scratch

def Frame (s t : Store) : Prop := ∀ j, j ∉ scratch → j ≠ 244 → t j = s j

def Bounded (s : Store) (L : ℕ) : Prop := ∀ j ∈ scratch, (s j).length ≤ L

theorem frame_refl (s : Store) : Frame s s := by
  intro j _ _
  rfl

theorem frame_trans {s t u : Store} (hst : Frame s t) (htu : Frame t u) : Frame s u := by
  intro j hj h244
  exact (htu j hj h244).trans (hst j hj h244)

theorem frame_update {s t : Store} (h : Frame s t) (j : Fin 256) (bits : List Bool)
    (hj : j ∈ scratch ∨ j = 244) : Frame s (Function.update t j bits) := by
  intro i hi h244
  have hij : i ≠ j := by
    intro he
    subst i
    rcases hj with hj | rfl
    · exact hi hj
    · exact h244 rfl
  simpa [hij] using h i hi h244

theorem bounded_update {s : Store} {L : ℕ} (h : Bounded s L) (j : Fin 256)
    (bits : List Bool) (hbits : bits.length ≤ L) : Bounded (Function.update s j bits) L := by
  intro i hi
  by_cases hij : i = j
  · subst i
    simpa using hbits
  · simpa [hij] using h i hi

theorem bounded_of_empty (s : Store) (L : ℕ) (h : ∀ j ∈ scratch, s j = []) :
    Bounded s L := by
  intro j hj
  simp [h j hj]

theorem node_port_mem (i : Fin 6) : SubexpNodeScanControl.ports i ∈ scratch := by
  fin_cases i <;> decide

theorem frame_node_work {s t : Store} (h : Frame s t) (w : Fin 6 → List Bool) :
    Frame s (SubexpNodeScanControl.work t w) := by
  intro j hj h244
  rw [SubexpNodeScanControl.work_frame]
  · exact h j hj h244
  · rintro ⟨i, rfl⟩
    exact hj (node_port_mem i)

theorem bounded_node_work {s : Store} {L : ℕ} (h : Bounded s L)
    (w : Fin 6 → List Bool) (hw : ∀ i, (w i).length ≤ L) :
    Bounded (SubexpNodeScanControl.work s w) L := by
  classical
  intro j hj
  by_cases hm : ∃ i, SubexpNodeScanControl.ports i = j
  · obtain ⟨i, rfl⟩ := hm
    simpa using hw i
  · rw [SubexpNodeScanControl.work_frame s w j hm]
    exact h j hj

theorem frame_initialized (s : Store) (D B : ℕ) :
    Frame s (SubexpLocalCRTSetup.initialized s D B) := by
  apply frame_update _ 229 _ (by decide)
  apply frame_update _ 217 _ (by decide)
  apply frame_update _ 215 _ (by decide)
  apply frame_update _ 240 _ (by decide)
  apply frame_update _ 220 _ (by decide)
  exact frame_update (frame_refl s) 242 _ (by decide)

theorem bounded_initialized (s : Store) (D B L : ℕ) (h : Bounded s L)
    (hz : (SubexpLocalCRTSetup.zeroArray D B).length ≤ L)
    (ho : (SubexpLocalCRTSetup.oneArray D B (s 207)).length ≤ L)
    (hnodes : (s 214).length ≤ L) (hindex : (s 216).length ≤ L) (hL : 1 ≤ L) :
    Bounded (SubexpLocalCRTSetup.initialized s D B) L := by
  apply bounded_update _ 229 [true] hL
  apply bounded_update _ 217 (s 216) hindex
  apply bounded_update _ 215 (s 214) hnodes
  apply bounded_update _ 240 _ ho
  apply bounded_update _ 220 _ ho
  exact bounded_update h 242 _ hz

theorem cleared_eq (s t : Store) (h : Frame s t) (hzero : ∀ j ∈ scratch, s j = []) :
    SubexpLocalCRTSetup.cleared scratch t = Function.update s 244 (t 244) := by
  funext j
  rw [SubexpLocalCRTSetup.cleared_apply]
  by_cases hj : j ∈ scratch
  · have h244 : j ≠ 244 := by
      intro he
      subst j
      exact (by decide : (244 : Fin 256) ∉ scratch) hj
    simp [hj, h244, hzero j hj]
  · by_cases h244 : j = 244
    · subst j
      simp [hj]
    · simp [hj, h244, h j hj h244]

theorem command_run (s t : Store) (L : ℕ) (h : Frame s t)
    (hzero : ∀ j ∈ scratch, s j = []) (hsize : Bounded t L) :
    ExecutesIn command (37 * (2 * L + 3)) t (Function.update s 244 (t 244)) := by
  have hc := SubexpLocalCRTSetup.clearMany_run scratch t L hsize
  rw [cleared_eq s t h hzero] at hc
  exact hc

theorem node_skip_length {A C : Type*} (f : A → C → A) (cs : List C)
    (x : SubexpNodeScanControl.Cursor A) :
    (SubexpNodeScanControl.run f cs x).skip.length ≤ x.skip.length := by
  induction cs generalizing x with
  | nil => exact le_rfl
  | cons c cs ih =>
      apply (ih (SubexpNodeScanControl.next f c x)).trans
      rcases x with ⟨a, skip, pending⟩
      cases skip with
      | nil => cases pending <;> simp [SubexpNodeScanControl.next]
      | cons b skip => simp [SubexpNodeScanControl.next]

theorem marker_length (b : Bool) : (SubexpNodeScanControl.marker b).length ≤ 1 := by
  cases b <;> decide

end SubexponentialSAT.SubexpLocalCRTFrames

end OAI.Algorithms
