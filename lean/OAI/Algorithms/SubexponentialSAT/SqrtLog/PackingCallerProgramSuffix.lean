import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingCallerProgramCleanup

namespace OAI.Algorithms

/-! Full native layout suffix followed by a paid metadata save and cleanup. -/
namespace SubexponentialSAT.SqrtLog.PackingCallerProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open PackingLoaderProgram

def suffix : Code := .seq prepareSuffix
  (.seq (.call (ProgramLinking.liftProgram LayoutProgram.NativePacking.program id lowPorts))
    (.seq (saveHigh 32 63) clearLow))

def suffixBudget {U : Type*} [DecidableEq U] (outside : Store)
    (s : LayoutProgram.NativePacking.Spec U) :=
  prepareBudget outside + LayoutProgram.NativePacking.budget s +
    (7*s.suffix.metadata.length+5) + clearLowBudget (s.suffix.outputState (fun _=>false))

theorem suffix_eval {U : Type*} [DecidableEq U] (outside : Store)
    (regs : Fin 16 → Bool) (s : LayoutProgram.NativePacking.Spec U)
    (hdelta : s.params.Δ=1) (h52 : outside 52=[]) (h63 : outside 63=[])
    (hD : SubexponentialSAT.BinaryArithmetic.toNat (outside 58)=s.params.D)
    (hwidth : outside 53=s.params.width)
    (halphabet : outside 54=ProgramEncoding.encodeRecords s.params.alphabet)
    (hplans : outside 61=s.params.planStream) (hwords : outside 62=s.params.rows.flatten) :
    ∃ t rf, t ≤ suffixBudget outside s ∧ Eval suffix t
      (framed outside (⟨regs,fun _=>[]⟩ : Small))
      (framed (Function.update outside 63 s.suffix.metadata) (⟨rf,fun _=>[]⟩ : Small)) := by
  obtain ⟨tp,rp,htp,hp⟩ := prepareSuffix_eval outside regs s.params hdelta h52 hD
    hwidth halphabet hplans hwords
  obtain ⟨tn,htn,rn,hn⟩ := LayoutProgram.NativePacking.program_trace s rp
  have hnative := framed_call LayoutProgram.NativePacking.program outside hn
  obtain ⟨rs,hs⟩ := saveHigh_eval outside (s.suffix.outputState rn) 32 63
    (by decide) (by decide) h52 h63
  have hmeta : (s.suffix.outputState rn).stacks 32=s.suffix.metadata := by
    simp [LayoutProgram.PackLabels.Spec.outputState,PackingProgram.outputState]
  rw [hmeta] at hs
  obtain ⟨rf,hclear⟩ := clearLow_run (Function.update outside 63 s.suffix.metadata)
    (setRegs (s.suffix.outputState rn) rs)
  have hclearCost : clearLowBudget (setRegs (s.suffix.outputState rn) rs)=
      clearLowBudget (s.suffix.outputState (fun _=>false)) := rfl
  rw [hclearCost] at hclear
  exact ⟨tp+(tn+((7*s.suffix.metadata.length+5)+
      clearLowBudget (s.suffix.outputState (fun _=>false)))),rf,
    by dsimp [suffixBudget]; omega,hp.seq (hnative.seq (hs.seq hclear))⟩

end SubexponentialSAT.SqrtLog.PackingCallerProgram

end OAI.Algorithms
