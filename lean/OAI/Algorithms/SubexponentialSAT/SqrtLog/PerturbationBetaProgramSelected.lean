import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram

namespace OAI.Algorithms

/-! One selected coefficient row is evaluated by the actual Horner command
and accumulated by the actual extension-ring addition service. -/
namespace SubexponentialSAT.SqrtLog.PerturbationBetaProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexpScanPrimitives SubexpLiftRing SubexpQuarticRing
open CRTLocalProgram (LowFrame lowFrame_update lowFrame_refl)

def selectedBudget (n t d : ℕ) : ℕ :=
  HornerProgram.modelBudget n t d + HornerProgram.Services.addBudget (baseWidth 3 t) d +
    32*(d*baseWidth 3 t)+7*n+36

def nextValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (P : List (RingProgram.Code (RingProgram.ScalarCode 3 t) d))
    (theta acc : RingProgram.Code (RingProgram.ScalarCode 3 t) d) :=
  ((RingProgram.modelProgram t a M cache).addRun
    (HornerProgram.modelValue t a M cache P theta) acc).1

theorem selected_run (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (s : Store) (hready : HornerProgram.Services.NativeReady 3 t M cache
      (HornerProgram.modelTable t a M cache) s)
    (P : List (RingProgram.Code (RingProgram.ScalarCode 3 t) d))
    (theta acc : RingProgram.Code (RingProgram.ScalarCode 3 t) d)
    (hP : s 246=HornerProgram.encodePolynomial RingProgram.flat P)
    (hx : s 247=RingProgram.flat theta) (ha : s 220=RingProgram.flat acc)
    (hz0 : s 207=RingProgram.flat (RingProgram.modelProgram t a M cache).zeroRun.1)
    (hc : (s 210).length=P.length) (hw : (s 250).length=d*baseWidth 3 t)
    (h240 : s 240=[]) (h248 : s 248=[]) (h241 : s 241=[])
    (h244 : s 244=[]) (h245 : s 245=[]) (h251 : s 251=[]) (h252 : s 252=[]) :
    ExecutesIn selected (selectedBudget P.length t d) s
      (Function.update (Function.update s 246 []) 220
        (RingProgram.flat (nextValue t a M cache P theta acc))) := by
  let W := d*baseWidth 3 t
  let v := HornerProgram.modelValue t a M cache P theta
  let z := (RingProgram.modelProgram t a M cache).zeroRun.1
  let out := nextValue t a M cache P theta acc
  let s1 := Function.update s 240 (RingProgram.flat z)
  let s2 := Function.update s1 248 (s 210)
  let s3 := Function.update (Function.update (Function.update s2 246 []) 240 (RingProgram.flat v)) 248 []
  let s4 := Function.update s3 241 (RingProgram.flat acc)
  let s5 := Function.update s4 240 (RingProgram.flat out)
  let s6 := Function.update s5 241 []
  let s7 := Function.update s6 220 []
  have hf1 : LowFrame s s1 := lowFrame_update (lowFrame_refl s) 240 (by decide) _
  have hf2 : LowFrame s s2 := lowFrame_update hf1 248 (by decide) _
  have hf3 : LowFrame s s3 := lowFrame_update (lowFrame_update
    (lowFrame_update hf2 246 (by decide) _) 240 (by decide) _) 248 (by decide) _
  have hf4 : LowFrame s s4 := lowFrame_update hf3 241 (by decide) _
  have h1 : ExecutesIn (copy 207 240) (7*W+5) s s1 := by
    simpa [s1,z,hz0,h240,RingProgram.flat_length,W] using
      copy_run 207 240 s (by decide) (by decide) (by decide) hready.workspace.1
  have h2 : ExecutesIn (copy 210 248) (7*P.length+5) s1 s2 := by
    simpa [s2,s1,h248,hc] using copy_run 210 248 s1
      (by decide) (by decide) (by decide) (by simp [s1,hready.workspace.1])
  have h3 : ExecutesIn HornerProgram.modelCommand (HornerProgram.modelBudget P.length t d) s2 s3 := by
    exact HornerProgram.modelCommand_run t a M cache hz s2 (hready.frame hf2) P theta
      (by simp [s2,s1,hP]) (by simp [s2,s1,hx]) (by simp [s2,s1,z])
      (by simp [s2,hc]) (by simp [s2,s1,hw]) (by simp [s2,s1,h241])
      (by simp [s2,s1,h244]) (by simp [s2,s1,h245])
      (by simp [s2,s1,h251]) (by simp [s2,s1,h252])
  have h4 : ExecutesIn (copy 220 241) (7*W+5) s3 s4 := by
    simpa [s4,s3,s2,s1,ha,h241,RingProgram.flat_length,W] using
      copy_run 220 241 s3 (by decide) (by decide) (by decide)
        (by simp [s3,s2,s1,hready.workspace.1])
  have h5 : ExecutesIn (CRTLocalProgram.binaryStep HornerProgram.Services.add)
      (HornerProgram.Services.addBudget (baseWidth 3 t) d+8*W+9) s4 s5 := by
    exact CRTLocalProgram.binaryStep_run s RingProgram.flat HornerProgram.Services.add
      (fun x y => ((RingProgram.modelProgram t a M cache).addRun x y).1)
      (HornerProgram.Services.addBudget (baseWidth 3 t) d) W
      (HornerProgram.Services.add_spec 3 t M cache (HornerProgram.modelTable t a M cache) s hready)
      (fun x => (RingProgram.flat_length x).le) s4 v acc hf4
      (by simp [s4,s3]) (by simp [s4]) (by simp [s4,s3,s2,s1,h244])
      (by simp [s4,s3,s2,s1,h245])
  have h6 : ExecutesIn (clear 241) (2*W+3) s5 s6 := by
    simpa [s6,s5,s4,RingProgram.flat_length,W] using clear_run 241 s5
  have h7 : ExecutesIn (clear 220) (2*W+3) s6 s7 := by
    simpa [s7,s6,s5,s4,s3,s2,s1,ha,RingProgram.flat_length,W] using clear_run 220 s6
  have he : Function.update (Function.update s7 240 []) 220 (RingProgram.flat out) =
      Function.update (Function.update s 246 []) 220 (RingProgram.flat out) := by
    funext i
    by_cases h0 : i=240 <;> by_cases h1 : i=248 <;> by_cases h2 : i=246 <;>
      by_cases h3 : i=241 <;> by_cases h4 : i=220 <;>
      simp [s7,s6,s5,s4,s3,s2,s1,h0,h1,h2,h3,h4,h240,h248,h241]
  have h8 : ExecutesIn (SubexpPolynomialConstructor.move 240 220) (6*W+6) s7
      (Function.update (Function.update s 246 []) 220 (RingProgram.flat out)) := by
    have h := SubexpPolynomialConstructor.move_run s7 240 220
      (by decide) (by decide) (by decide) (by simp [s7,s6,s5,s4,s3,s2,s1,h245])
      (by simp [s7])
    have hv : s7 240=RingProgram.flat out := by simp [s7,s6,s5]
    rw [hv,he] at h
    simpa only [RingProgram.flat_length] using h
  have h := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))
  convert h using 1 <;> first | (simp only [selectedBudget]; dsimp [W]; omega) | rfl

end SubexponentialSAT.SqrtLog.PerturbationBetaProgram

end OAI.Algorithms
