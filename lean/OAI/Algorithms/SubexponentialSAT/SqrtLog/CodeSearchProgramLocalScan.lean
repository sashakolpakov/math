import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramCallback
import OAI.Algorithms.SubexponentialSAT.RecordMappedPrograms
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCodeSearch

namespace OAI.Algorithms

/-! All-word iteration with a proved physical callback. Every visited word,
including each failed witness, pays for parsing, copies, arithmetic and cleanup. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

 def localPorts : RecordPrograms.Ports 16 24 where
  tag := 13
  present := 14
  found := 15
  source := 21
  payload := 22
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

def LocalReady {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (d : ℕ) (a : SearchState) : Prop :=
  WorkEmpty a ∧ a.stacks 18 = matrixFrames Q ∧ a.stacks 19 = List.replicate t true ∧
    a.stacks 20 = List.replicate d true ∧ a.stacks 23 = []

abbrev localScanCommand : Cmd 16 24 := RecordPrograms.iterate localPorts wordCallback

def localScanProgram := compiled localScanCommand 21 21

theorem local_word_contract {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3) (d : ℕ) :
    RecordMappedPrograms.Contract localPorts wordCallback
      (fun x => scalarFrames (List.ofFn x)) (fun x => decide (wordRejects Q x d))
      (fun _ => callbackBudget t D d) (LocalReady Q d) := by
  intro x tail base hb
  let a := RecordPrograms.state localPorts base false true false tail
    (scalarFrames (List.ofFn x)).reverse
  have ha : LocalReady Q d a := by
    rcases hb with ⟨he,hm,ht,hd,h23⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i
      have hi21 : wordStacks i ≠ (21 : Fin 24) := by
        intro h; have hv := congrArg Fin.val h
        simp [wordStacks] at hv
        omega
      have hi22 : wordStacks i ≠ (22 : Fin 24) := by
        intro h; have hv := congrArg Fin.val h
        simp [wordStacks] at hv
        omega
      simpa [a, RecordPrograms.state, localPorts, hi21, hi22] using he i
    all_goals simpa [a, RecordPrograms.state, localPorts] using (by assumption)
  obtain ⟨n,out,hn,he,hemp,hf,h13,h14,h22,hframe⟩ := wordCallback_eval Q x d a
    ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2 (by
      simp [a, RecordPrograms.state, localPorts])
  have hout : LocalReady Q d out := by
    refine ⟨hemp, ?_, ?_, ?_, ?_⟩
    · exact (hframe 18 (by decide) (by decide)).trans ha.2.1
    · exact (hframe 19 (by decide) (by decide)).trans ha.2.2.1
    · exact (hframe 20 (by decide) (by decide)).trans ha.2.2.2.1
    · exact (hframe 23 (by decide) (by decide)).trans ha.2.2.2.2
  have hstate : RecordPrograms.state localPorts out false true
      (decide (wordRejects Q x d)) tail [] = out := by
    apply RecordPrograms.state_eq_self
    · simpa [a, localPorts, RecordPrograms.state] using h13
    · simpa [a, localPorts, RecordPrograms.state] using h14
    · exact hf
    · simpa [a, localPorts, RecordPrograms.state] using hframe 21 (by decide) (by decide)
    · exact h22
  exact ⟨n,out,hn,hout,hstate.symm ▸ he⟩

theorem localScan_eval {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3) (d : ℕ)
    (values : List (Fin D → SparseCode.F3)) (suffix : List Bool) (base : SearchState)
    (hb : LocalReady Q d base) (v pr f : Bool) :
    ∃ (n : ℕ) (out : SearchState),
      n ≤ 3 + values.length * (30 * D + callbackBudget t D d + 7) ∧
      LocalReady Q d out ∧
      Eval localScanCommand n
        (RecordPrograms.state localPorts base v pr f
          (Encoding.encodeList (fun x => scalarFrames (List.ofFn x)) values ++ suffix) [])
        (RecordPrograms.state localPorts out false true
          (values.any (fun x => decide (wordRejects Q x d)))
          (RecordMappedPrograms.unread (fun x => scalarFrames (List.ofFn x))
            (fun x => decide (wordRejects Q x d)) values suffix) []) := by
  obtain ⟨n,out,hn,hout,he⟩ := RecordMappedPrograms.iterate_run localPorts wordCallback
    (fun x => scalarFrames (List.ofFn x)) (fun x => decide (wordRejects Q x d))
    (fun _ => callbackBudget t D d) (LocalReady Q d) (local_word_contract Q d)
    values suffix base hb v pr f
  refine ⟨n,out,?_,hout,he⟩
  have hbudget : RecordMappedPrograms.budget (fun x => scalarFrames (List.ofFn x))
      (fun _ => callbackBudget t D d) values =
        values.length * (30 * D + callbackBudget t D d + 7) := by
    generalize values = vs
    induction vs with
    | nil => simp [RecordMappedPrograms.budget]
    | cons x xs ih =>
        simp only [RecordMappedPrograms.budget, scalarFrames_ternary_length,
          List.length_ofFn, List.length_cons, ih]
        ring
  rw [hbudget] at hn
  exact hn

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
