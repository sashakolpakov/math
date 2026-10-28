import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationBetaProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationEmitProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationMaskProgram

namespace OAI.Algorithms

/-! Per-coordinate physical composition. Original ambient variable IDs remain
unchanged throughout row loading, singleton support construction and emission. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl SubexpPolynomialConstructor

/-- Read one runtime-framed row, then construct the current support mask. -/
def loadCoordinate : Code := .seq PerturbationBetaProgram.readRow
  (.seq (move 246 219) PerturbationMaskProgram.command)

def coordinateLoadScratch : List (Fin 256) := [120,214,219,221,222,223,232,245,246]

def coordinateLoaded (s : Store) (bits rest mask : List Bool) : Store :=
  Function.update (Function.update (Function.update s 230 rest) 219 bits) 214 mask

theorem loadCoordinate_run {n : ℕ} (s : Store) (v : Fin n) (bits rest : List Bool)
    (hrow : s 230=true::(Encoding.frame bits++rest))
    (hn : (s 212).length=n) (hv : (s 218).length=v.val)
    (he : ∀ i ∈ coordinateLoadScratch, s i=[]) :
    ExecutesIn loadCoordinate (15*bits.length+11*n+17*v.val+38) s
      (coordinateLoaded s bits rest (Squarefree.encodeMask {v})) := by
  let s1 := Function.update (Function.update s 230 rest) 246 bits
  let s2 := Function.update (Function.update s 230 rest) 219 bits
  have h1 : ExecutesIn PerturbationBetaProgram.readRow (9*bits.length+8) s s1 :=
    PerturbationBetaProgram.readRow_run s bits rest hrow
      (he 232 (by simp [coordinateLoadScratch])) (he 246 (by simp [coordinateLoadScratch]))
  have hout : Function.update (Function.update s1 246 []) 219 (s1 246)=s2 := by
    funext i
    by_cases h219 : i=219 <;> by_cases h230 : i=230 <;> by_cases h246 : i=246 <;>
      simp [s1,s2,h219,h230,h246,he 246 (by simp [coordinateLoadScratch])]
  have h2 : ExecutesIn (move 246 219) (6*bits.length+6) s1 s2 := by
    have h := move_run s1 246 219 (by decide) (by decide) (by decide)
      (by simpa [s1] using he 245 (by simp [coordinateLoadScratch]))
      (by simpa [s1] using he 219 (by simp [coordinateLoadScratch]))
    rw [hout] at h
    simpa [s1] using h
  have h3 : ExecutesIn PerturbationMaskProgram.command (11*n+17*v.val+24) s2
      (coordinateLoaded s bits rest (Squarefree.encodeMask {v})) := by
    apply PerturbationMaskProgram.singleton_run s2 v
    all_goals first | simpa [s2] using hn | simpa [s2] using hv |
      simpa [s2] using he _ (by simp [coordinateLoadScratch])
  have hcost : 9 * bits.length + 8 +
      (6 * bits.length + 6 + (11 * n + 17 * v.val + 24)) =
      15 * bits.length + 11 * n + 17 * v.val + 38 := by omega
  rw [← hcost]
  exact h1.seq (h2.seq h3)

/-- The array is the actual output of the fixed native shift command. -/
def finishCoordinate : Code := .seq (shift DensePolynomialProgram.Fixed.mulCommand
  DensePolynomialProgram.AddService.command) (.seq PerturbationEmitProgram.command
    (.seq (clear 214) PerturbationMaskProgram.advance))

def coordinateEmitScratch : List (Fin 256) := [120,221,222,223,224,225,226,227,228]

/-- Sequential composition exposes the exact output bytes, including their
prepend order. The supplied trace is discharged by native_shift_run. -/
theorem finishCoordinate_run (s : Store) (mask : List Bool) (W K : ℕ)
    (cs : List (List Bool)) (hc : ∀ c ∈ cs,c.length=W)
    (hs : ExecutesIn (shift DensePolynomialProgram.Fixed.mulCommand
      DensePolynomialProgram.AddService.command) K s
      (Function.update (Function.update s 219 []) 240 (PerturbationEmitProgram.array cs)))
    (hJ : s 213=List.replicate cs.length true) (hw : (s 211).length=W)
    (hm : s 214=mask) (he : ∀ i ∈ coordinateEmitScratch,s i=[])
    (h240 : s 240=[]) :
    ExecutesIn finishCoordinate
      (K+PerturbationEmitProgram.budget cs.length mask.length W+2*mask.length+5) s
      (Function.update (Function.update (Function.update (Function.update s 219 [])
        217 (PerturbationEmitProgram.emitted mask 1 cs.tail (s 217))) 214 [])
        218 (true::s 218)) := by
  let s1 := Function.update (Function.update s 219 []) 240 (PerturbationEmitProgram.array cs)
  let s2 := Function.update (Function.update s 219 [])
    217 (PerturbationEmitProgram.emitted mask 1 cs.tail (s 217))
  let s3 := Function.update s2 214 []
  have hout : Function.update (Function.update s1 240 []) 217
      (PerturbationEmitProgram.emitted mask 1 cs.tail (s1 217))=s2 := by
    funext i
    by_cases h219 : i=219 <;> by_cases h217 : i=217 <;> by_cases h240' : i=240 <;>
      simp [s1,s2,h219,h217,h240',h240]
  have h2 : ExecutesIn PerturbationEmitProgram.command
      (PerturbationEmitProgram.budget cs.length mask.length W) s1 s2 := by
    have h := PerturbationEmitProgram.command_run s1 mask W cs hc
      (by simp [s1]) (by simpa [s1] using hJ) (by simpa [s1] using hw)
      (by simpa [s1] using hm)
      (by simpa [s1] using he 120 (by simp [coordinateEmitScratch]))
      (by simpa [s1] using he 221 (by simp [coordinateEmitScratch]))
      (by simpa [s1] using he 222 (by simp [coordinateEmitScratch]))
      (by simpa [s1] using he 223 (by simp [coordinateEmitScratch]))
      (by simpa [s1] using he 224 (by simp [coordinateEmitScratch]))
      (by simpa [s1] using he 225 (by simp [coordinateEmitScratch]))
      (by simpa [s1] using he 226 (by simp [coordinateEmitScratch]))
      (by simpa [s1] using he 227 (by simp [coordinateEmitScratch]))
      (by simpa [s1] using he 228 (by simp [coordinateEmitScratch]))
    rw [hout] at h
    exact h
  have h3 : ExecutesIn (clear 214) (2*mask.length+3) s2 s3 := by
    simpa [s3,s2,hm] using clear_run 214 s2
  have h4 := PerturbationMaskProgram.advance_run s3
  have h := hs.seq (h2.seq (h3.seq h4))
  have hcost : K + (PerturbationEmitProgram.budget cs.length mask.length W +
      (2 * mask.length + 3 + 2)) =
      K + PerturbationEmitProgram.budget cs.length mask.length W +
        2 * mask.length + 5 := by omega
  rw [← hcost]
  simpa [finishCoordinate, s3, s2] using h

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
