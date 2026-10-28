import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramLookupPair

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem lookup_lifted {R S : ℕ} (register : Fin 6 → Fin R) (stack : Fin 16 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (a : State R S) (records : List (List Bool × List Bool)) (row col : List Bool)
    (mr mc : GlobalBasisMetadata.Metadata)
    (hr : records.lookup row=some mr.encode) (hc : records.lookup col=some mc.encode)
    (ha : projectState register stack a=LookupPair.state (a.regs ∘ register)
      (SelectorProgram.rawRecords records) row col [] [] [] [] [] []) :
    ∃ n ≤ 400*(GlobalBasisMetadata.volume records row)^2+
        400*(GlobalBasisMetadata.volume records col)^2+1,
      ∃ e : State R S,
      Eval (.call (ProgramLinking.liftProgram LookupPair.program register stack)) n a e ∧
      projectState register stack e=
        LookupPair.state ![false,false,false,false,mr.coveredFlag,mc.coveredFlag]
          (SelectorProgram.rawRecords records) row col mr.block mr.typeCode mr.rank
            mc.block mc.typeCode mc.rank ∧
      (∀ j, (¬ ∃ i, stack i=j) → e.stacks j=a.stacks j) ∧
      (∀ j, (¬ ∃ i, register i=j) → e.regs j=a.regs j) := by
  obtain ⟨n,hn,he⟩ := LookupPair.program_runsIn records row col mr mc hr hc (a.regs ∘ register)
  rw [← ha] at he
  let b := LookupPair.state ![false,false,false,false,mr.coveredFlag,mc.coveredFlag]
    (SelectorProgram.rawRecords records) row col mr.block mr.typeCode mr.rank
      mc.block mc.typeCode mc.rank
  refine ⟨n,hn,embedState register stack a b,
    eval_call_from_state LookupPair.program register stack a hregister hstack he,?_,?_,?_⟩
  · exact projectState_embed register stack a b hregister hstack
  · exact fun j hj => embedState_stack_frame register stack a b j hj
  · exact fun j hj => embedState_register_frame register stack a b j hj

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBankFrame

end OAI.Algorithms
