import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgramMerge

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

def cost (words : List (List Bool)) (mask : List Bool) : ℕ :=
  7*(ProgramEncoding.encodeRecords words).length+9*words.flatten.length+
    6*words.length+22*mask.length+29

theorem command_eval (regs : Fin 4 → Bool) (words : List (List Bool)) (mask : List Bool)
    (hh : words.flatten.length = HighIncidenceProgram.Restriction.highCount mask) :
    ∃ n rf, n ≤ cost words mask ∧ Eval command n
      (state regs (ProgramEncoding.encodeRecords words) mask [] [] [] [] [] [] [] [])
      (state rf (ProgramEncoding.encodeRecords words) mask mask.reverse
        (HighIncidenceProgram.Restriction.zeroMerge mask words.flatten).reverse [] [] [] [] [] []) := by
  obtain ⟨nm,rm,hnm,hem⟩ := mask_eval regs (ProgramEncoding.encodeRecords words) mask
  have hec := copy_counter_eval rm (ProgramEncoding.encodeRecords words) mask mask.reverse
  obtain ⟨nf,rf,hnf,hef⟩ := flatten_eval (readRegs rm 0 1 none) words mask mask.reverse
  have hecm := copy_mask_eval rf (ProgramEncoding.encodeRecords words) mask mask.reverse words.flatten
  obtain ⟨nh,rh,hnh,heh⟩ := merge_eval (readRegs rf 0 1 none)
    (ProgramEncoding.encodeRecords words) mask mask.reverse words.flatten hh
  refine ⟨nm+(7*(ProgramEncoding.encodeRecords words).length+5+
    (nf+(7*mask.length+5+nh))),rh,?_,hem.seq (hec.seq (hef.seq (hecm.seq heh)))⟩
  unfold cost
  omega

theorem runsIn (regs : Fin 4 → Bool) (words : List (List Bool)) (mask : List Bool)
    (hh : words.flatten.length = HighIncidenceProgram.Restriction.highCount mask) :
    ∃ rf, RunsIn program (cost words mask+1)
      ((state regs (ProgramEncoding.encodeRecords words) mask [] [] [] [] [] [] [] []).withPC
        (some program.entry))
      ((state rf (ProgramEncoding.encodeRecords words) mask mask.reverse
        (HighIncidenceProgram.Restriction.zeroMerge mask words.flatten).reverse [] [] [] [] [] []).withPC none) := by
  obtain ⟨n,rf,hn,he⟩ := command_eval regs words mask hh
  exact ⟨rf,n+1,by omega,compiled_halt_trace he 0 3⟩


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
