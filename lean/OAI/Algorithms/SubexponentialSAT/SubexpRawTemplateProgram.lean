import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateGroupLoop
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateOuter
import OAI.Algorithms.SubexponentialSAT.SubexpRawTemplateControl
import OAI.Algorithms.SubexponentialSAT.SubexpFactorRoutingControl
import OAI.Algorithms.SubexponentialSAT.Subexp.SupportSelectionProgram

namespace OAI.Algorithms

/-!
# The fixed raw template producer

The program consumes the actual bank bundle and complete factor packet
master. It derives supports from packing metadata and routes factors by
their actual assignment words. The common groups are built once, then
physically copied into every outer block. No grouped-data callback occurs.
-/

namespace SubexponentialSAT.SubexpRawTemplate

open BitProgram StructuredCalls

def factorPort : Fin 48 → Fin 288 := ![258, 225, 219, 116, 261, 260, 210, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]
def supportPort : Fin 64 → Fin 288 := ![209, 223, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 109, 219, 116, 269, 172, 173, 174, 175, 261, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201]

theorem factorPort_injective : Function.Injective factorPort := by decide

private def supportPortLeft (i : Fin 288) : Fin 64 :=
  if i = 209 then 0
  else if i = 223 then 1
  else if i = 109 then 30
  else if i = 219 then 31
  else if i = 116 then 32
  else if i = 269 then 33
  else if i = 261 then 38
  else Fin.ofNat 64 (i.val - 138)

private theorem supportPortLeft_apply (i : Fin 64) :
    supportPortLeft (supportPort i) = i := by
  fin_cases i <;> rfl

theorem supportPort_injective : Function.Injective supportPort :=
  Function.LeftInverse.injective supportPortLeft_apply

def selectFactors : Code := .call (ProgramLinking.liftProgram
  SubexpFactorRoutingControl.program id factorPort)

def selectSupport : Code := .call (ProgramLinking.liftProgram
  Subexp.SupportSelectionProgram.program id supportPort)

/-- Produce outside support even when there are no color groups. The
initial color support is discarded; later selections use the same actual
metadata procedure for the current color. -/
def initializeOutside : Code :=
  .seq selectSupport (.seq (clear 209) (.seq (transfer 223 224) (transfer 224 208)))

def groupBody : Code :=
  .seq (capture 204 206 (by decide))
    (.seq selectFactors (.seq selectSupport (.seq (clear 223)
      (.seq groupCommand (.seq (appendRecord 216 211) (.seq (clear 216)
        (.seq (clear 209) (.seq (clear 210) incrementColor))))))))

def closeGroups : Code :=
  .seq (pushBit 211 false) (.seq (transfer 211 212) (clear 219))

/-- These are generated temporary masters, not immutable source data. -/
def cleanup : Code := .seq (clear 208) (.seq (clear 212)
  (.seq (clear 225) (.seq (clear 226) (clear 227))))

def command : Code := .seq initializeOutside (.seq splitBanks
  (.seq (scanBare 204 groupBody) (.seq closeGroups (.seq outerCommand cleanup))))

abbrev program : Program 16 288 (size command + 1) := compiled command 204 15

end SubexponentialSAT.SubexpRawTemplate

end OAI.Algorithms
