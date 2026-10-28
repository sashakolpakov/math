import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramScan
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramInverseConstants
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgramCorrection

namespace OAI.Algorithms

/-! The fixed native local-Hermite controller. Ring precision is read from212
and jet order from243. Protected polynomial service metadata192/193 are
prepared by the caller. All arithmetic calls are ordinary finite programs. -/
namespace SubexponentialSAT.SqrtLog.CRTLocalProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

def initializeLocal : Code :=
  SubexpPolynomialConstructor.construct 207 104 240 ;;
  copy 214 215 ;; copy 216 217 ;; SubexpLocalCRTSetup.token 229

def prepareLocalInverse (sm sa : Code) : Code :=
  SubexpLocalCRTSetup.clearMany [217,229] ;;
  replace 240 223 ;; clear 240 ;; constantCommand ;;
  inverseConstantsCommand sm sa ;;
  SubexpPolynomialConstructor.construct 207 104 220 ;;
  copy 192 242

def positiveLocal (sm sa pm pa : Code) : Code :=
  initializeLocal ;; scanCommand sm sa pm ;; prepareLocalInverse sm sa ;;
  correctionCommand pm pa ;; SubexpLocalCRTSetup.clearMany [220,223,227,228,242]

def localCommand (sm sa pm pa : Code) : Code :=
  test 243 15 ;; .ite 15 (positiveLocal sm sa pm pa) (.base .skip)

def localProgram (sm sa pm pa : Code) := compiled (localCommand sm sa pm pa) 225 244

end SubexponentialSAT.SqrtLog.CRTLocalProgram

end OAI.Algorithms
