import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramLocalScan
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramGeneratedWords
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LocalCodeRejection

namespace OAI.Algorithms

/-! Complete physical local-code verification, independent of candidate order.
The input records are exactly the output bytes of the fixed tuple generator.
The bound charges every word, even when the run stops at an earlier witness. -/
namespace SubexponentialSAT.SqrtLog.CodeSearchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def localVerifierBudget (t D d : ℕ) :=
  4 + 3 ^ D * (30 * D + callbackBudget t D d + 7)

theorem local_verifier_runsIn {t D : ℕ}
    (Q : Fin t → Fin D → SparseCode.F3) (d : ℕ) (base : SearchState)
    (hb : LocalReady Q d base) (v pr f : Bool) :
    ∃ (out : SearchState) (found : Bool) (tail : List Bool),
      LocalReady Q d out ∧ (found = false ↔ SparseCode.HasDistance Q d) ∧
      RunsIn localScanProgram (localVerifierBudget t D d)
        ((RecordPrograms.state localPorts base v pr f
          (ProgramEncoding.encodeRecords (framedCandidates 3 D)) []).withPC
            (some localScanProgram.entry))
        ((RecordPrograms.state localPorts out false true found tail []).withPC none) := by
  obtain ⟨values,hvalues,hlen,hcomplete⟩ := generated_words_typed D
  obtain ⟨n,out,hn,hout,he⟩ := localScan_eval Q d values [] base hb v pr f
  have hinput : Encoding.encodeList (fun x => scalarFrames (List.ofFn x)) values =
      ProgramEncoding.encodeRecords (framedCandidates 3 D) := by
    rw [encodeList_map_records, hvalues]
  have hspec := LocalCode.complete_list_any_rejection_eq_false_iff (d := d) values hcomplete Q
  refine ⟨out, values.any (fun x => decide (wordRejects Q x d)),
    RecordMappedPrograms.unread (fun x => scalarFrames (List.ofFn x))
      (fun x => decide (wordRejects Q x d)) values [], hout, ?_, ?_⟩
  · exact hspec
  · refine ⟨n + 1, ?_, ?_⟩
    · unfold localVerifierBudget
      rw [hlen] at hn
      omega
    · have h := compiled_halt_trace he 21 21
      simpa only [localScanProgram, List.append_nil, hinput] using h

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
