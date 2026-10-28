import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBasisStage
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBankStage
import OAI.Algorithms.SubexponentialSAT.SubexpNodeOriginStage
import OAI.Algorithms.SubexponentialSAT.SubexpFactorPacketProgram
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateProgram

namespace OAI.Algorithms

/-!
# The fixed current-node blueprint producer

All five calls below are concrete finite programs. The basis and bank
stages read the protected static inputs; the origin stage reduces the
current Taylor cache; the packet and raw-template stages preserve encounter
order. Their data-format and readiness theorems must still be joined to
obtain the full per-node semantic contract.
-/

namespace SubexponentialSAT.SubexpNodeBlueprintStage

open BitProgram StructuredCalls

abbrev Data := State 16 288

abbrev command : Cmd 16 288 :=
  .seq (.call SubexpNodeBasisStage.program)
    (.seq (.call SubexpNodeBankStage.program)
      (.seq (.call SubexpNodeOriginStage.program)
        (.seq (.call SubexpFactorPacketProgram.program)
          (.call SubexpRawTemplate.program))))

abbrev program : Program 16 288 (size command + 1) := compiled command 116 15

/-- Measured composition of the actual finite producer calls. This lemma
does not replace any producer's input-layout or output-meaning proof. -/
theorem program_trace {n0 n1 n2 n3 n4 : ℕ} {d0 d1 d2 d3 d4 d5 : Data}
    (h0 : Trace SubexpNodeBasisStage.program n0
      (d0.withPC (some SubexpNodeBasisStage.program.entry)) (d1.withPC none))
    (h1 : Trace SubexpNodeBankStage.program n1
      (d1.withPC (some SubexpNodeBankStage.program.entry)) (d2.withPC none))
    (h2 : Trace SubexpNodeOriginStage.program n2
      (d2.withPC (some SubexpNodeOriginStage.program.entry)) (d3.withPC none))
    (h3 : Trace SubexpFactorPacketProgram.program n3
      (d3.withPC (some SubexpFactorPacketProgram.program.entry)) (d4.withPC none))
    (h4 : Trace SubexpRawTemplate.program n4
      (d4.withPC (some SubexpRawTemplate.program.entry)) (d5.withPC none)) :
    Trace program (n0 + (n1 + (n2 + (n3 + n4))) + 1)
      (d0.withPC (some program.entry)) (d5.withPC none) :=
  compiled_halt_trace ((Eval.call _ h0).seq
    ((Eval.call _ h1).seq ((Eval.call _ h2).seq
      ((Eval.call _ h3).seq (Eval.call _ h4))))) 116 15

end SubexponentialSAT.SubexpNodeBlueprintStage

end OAI.Algorithms
