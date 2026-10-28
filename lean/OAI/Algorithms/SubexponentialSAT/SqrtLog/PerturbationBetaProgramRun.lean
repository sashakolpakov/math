import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgramLoop
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgramFraming

namespace OAI.Algorithms

/-! Closed native beta scan from preserved row/choice masters. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing
open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)

def betaCommand : Code := .seq prepareInput (.seq (.seq peekRow loop) finish)
def betaMachine := compiled betaCommand 205 220

def workPorts : List (Fin 256) := [220,230,231,232,240,241,244,245,246,247,248,250,251,252]
def WorkEmpty (s : Store) : Prop := ∀ i∈workPorts,s i=[]

def staged (s : Store) : Store :=
  Function.update (Function.update s 247 (s 209)) 250 (s 211)

def runValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (theta : Coeff t d) (rows : List (List (Coeff t d) × Bool)) : Coeff t d :=
  rows.foldl (stepValue t a M cache theta) (RingProgram.modelProgram t a M cache).zeroRun.1

def runBudget (s : Store) (n L t d : ℕ) : ℕ :=
  initBudget s+n*(stepBudget L t d+2)+2+(4*(d*baseWidth 3 t)+14)

theorem betaCommand_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (base : Store) (hready : HornerProgram.Services.NativeReady 3 t M cache
      (HornerProgram.modelTable t a M cache) base)
    (theta : Coeff t d) (rows : List (List (Coeff t d) × Bool)) (L : ℕ)
    (hL : ∀ row∈rows,row.1.length=L)
    (h205 : base 205=rowsBits rows) (h206 : base 206=rows.map Prod.snd)
    (h207 : base 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (h209 : base 209=RingProgram.flat theta)
    (h210 : (base 210).length=L) (h211 : (base 211).length=d*baseWidth 3 t)
    (he : WorkEmpty base) :
    ExecutesIn betaCommand (runBudget base rows.length L t d) base
      (Function.update base 220 (RingProgram.flat (runValue t a M cache theta rows))) := by
  have hemp (i : Fin 256) (hi : i∈workPorts) := he i hi
  let z := (RingProgram.modelProgram t a M cache).zeroRun.1
  have hinit : initialized base=ready (staged base) rows z := by
    funext i
    by_cases h0 : i=230 <;> by_cases h1 : i=231 <;> by_cases h2 : i=220 <;>
      by_cases h3 : i=247 <;> by_cases h4 : i=250 <;>
      simp [initialized,ready,staged,Function.update_apply,h0,h1,h2,h3,h4,h205,h206,h207,z]
  have h1 := prepareInput_run base hready.workspace.1
    (hemp 230 (by simp [workPorts])) (hemp 231 (by simp [workPorts]))
    (hemp 220 (by simp [workPorts])) (hemp 247 (by simp [workPorts]))
    (hemp 250 (by simp [workPorts]))
  rw [hinit] at h1
  have hframe : LowFrame base (staged base) :=
    lowFrame_update (lowFrame_update (lowFrame_refl base) 247 (by decide) _) 250 (by decide) _
  have h2 := traversal_run t a M cache hz (staged base) (hready.frame hframe) theta z rows L hL
    (by simp [staged,h209]) (by simp [staged,h207])
    (by simp [staged,h210]) (by simp [staged,h211])
    (by simpa [staged] using hemp 232 (by simp [workPorts]))
    (by simpa [staged] using hemp 240 (by simp [workPorts]))
    (by simpa [staged] using hemp 246 (by simp [workPorts]))
    (by simpa [staged] using hemp 248 (by simp [workPorts]))
    (by simpa [staged] using hemp 241 (by simp [workPorts]))
    (by simpa [staged] using hemp 244 (by simp [workPorts]))
    (by simpa [staged] using hemp 245 (by simp [workPorts]))
    (by simpa [staged] using hemp 251 (by simp [workPorts]))
    (by simpa [staged] using hemp 252 (by simp [workPorts]))
  let out := runValue t a M cache theta rows
  let last := ready (staged base) [] out
  have hend : finished last=Function.update base 220 (RingProgram.flat out) := by
    funext i
    by_cases h0 : i=230 <;> by_cases h1 : i=231 <;> by_cases h2 : i=220 <;>
      by_cases h3 : i=247 <;> by_cases h4 : i=250 <;>
      simp [finished,last,ready,staged,h0,h1,h2,h3,h4,
        hemp 230 (by simp [workPorts]),hemp 231 (by simp [workPorts]),
        hemp 247 (by simp [workPorts]),hemp 250 (by simp [workPorts])]
  have hcost : finishBudget last=4*(d*baseWidth 3 t)+14 := by
    simp [finishBudget,last,ready,staged,rowsBits,Encoding.encodeList,h209,h211,RingProgram.flat_length]
    ring
  have h3 := finish_run last
  rw [hend,hcost] at h3
  have hall := h1.seq (h2.seq h3)
  convert hall using 1 <;> first | (simp only [runBudget]; omega) | rfl

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
