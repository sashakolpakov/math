import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLocalSeedProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLocalInitializedScan
import OAI.Algorithms.SubexponentialSAT.SubexpLocalGeometricProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLocalCRTFrames

namespace OAI.Algorithms

/-! The actual stages preserve the concrete arithmetic workspace needed by
the next stage. These lemmas discharge intermediate readiness from the
initial stored metadata and the proved full-frame endpoints. -/

namespace SubexponentialSAT.SubexpLocalReadiness

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpPolynomialPowerProgram

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))

abbrev Coeff := Coefficient p (D + 1)
abbrev Poly := FixedPolynomial p (D + 1) D

theorem not_changed_of_lt (j : Fin 256) (hj : j.val < 205) :
    j ∉ SubexpLocalInitializedScan.changed := by
  intro h
  simp only [SubexpLocalInitializedScan.changed, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [Fin.coe_ofNat_eq_mod] at hj

omit [Fact p.Prime] in
theorem geometric_of_scan (s : Store) (t z theta one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (width : List Bool) (frame : Fin 6 → List Bool)
    (H : SubexpLocalProductScan.Ready p D M s t z theta one minusOne width frame) :
    SubexpLocalGeometricProgram.Ready p D M s t width frame := by
  constructor
  · exact H.multiply
  · exact H.add
  · exact H.buffers
  · intro j hj
    apply H.scratch j
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide

theorem geometric_scanned (s : Store) (t z theta one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (width : List Bool) (frame : Fin 6 → List Bool)
    (nodes : List (Coeff p D)) (index : List Bool) (O : Poly p D)
    (H : SubexpLocalProductScan.Ready p D M (SubexpLocalInitializedScan.initial p D s)
      t z theta one minusOne width frame) :
    SubexpLocalGeometricProgram.Ready p D M
      (SubexpLocalInitializedScan.output p D M s t z theta one minusOne nodes index O)
      t width frame := by
  apply SubexpLocalGeometricProgram.ready_congr p D M
    (SubexpLocalInitializedScan.initial p D s) _ t width frame
    (geometric_of_scan p D M _ t z theta one minusOne width frame H)
  · exact SubexpLocalProductScan.scan_below _ _ _ _ _ _ _
  · exact SubexpNodeScanControl.work_frame _ _ 244 (by decide)
  · exact SubexpNodeScanControl.work_frame _ _ 245 (by decide)

omit [Fact p.Prime] in
theorem geometric_seed (s : Store) (t : Coeff p D) (width : List Bool) (frame : Fin 6 → List Bool)
    (H : SubexpLocalGeometricProgram.Ready p D M s t width frame)
    (a seed neg : List Bool) :
    SubexpLocalGeometricProgram.Ready p D M
      (SubexpLocalSeedProgram.prepared s D (baseWidth p (D + 1)) a seed neg)
      t width frame := by
  apply SubexpLocalGeometricProgram.ready_update p D M _ t width frame _ 228 _
    (by decide) (by decide) (by decide)
  apply SubexpLocalGeometricProgram.ready_update p D M _ t width frame _ 227 _
    (by decide) (by decide) (by decide)
  apply SubexpLocalGeometricProgram.ready_update p D M _ t width frame _ 208 _
    (by decide) (by decide) (by decide)
  exact SubexpLocalGeometricProgram.ready_update p D M s t width frame H 205 _
    (by decide) (by decide) (by decide)

theorem initialization_work_mem (j : Fin 256)
    (hj : j ∈ SubexpLocalInitializedScan.workPorts) : j ∈ SubexpLocalCRTFrames.scratch := by
  simp only [SubexpLocalInitializedScan.workPorts, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem seed_work_frame (j : Fin 256) (hj : j ∈ SubexpLocalSeedProgram.workPorts) :
    j ∉ SubexpLocalInitializedScan.changed ∧ j ∈ SubexpLocalCRTFrames.scratch := by
  simp only [SubexpLocalSeedProgram.workPorts, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    constructor <;> decide

theorem seed_scanned (s : Store) (t z theta one a : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (width : List Bool)
    (nodes : List (Coeff p D)) (index : List Bool) (O : Poly p D)
    (tail : List (Coeff p D))
    (harray : (SubexpNodeScanControl.run
      (SubexpLocalProductScan.stepValue p D M t z theta one minusOne)
      nodes ⟨O, index, true⟩).value.val = a :: tail)
    (hw : width.length = baseWidth p (D + 1))
    (hnative : ∀ i, s (SubexpLocalSeedProgram.powerPorts (SubexpQuarticPowerProgram.native i)) =
      SubexpQuarticPowerProgram.cleanNative M.bits (SubexpFlatAdd.encode t) width i)
    (hneg : ∀ i, s (SubexpLocalLinearFactorProgram.negatePorts i) =
      SubexpLocalSeedProgram.blankNegation minusOne.val M.bits width i)
    (hone : s 207 = SubexpFlatAdd.encode one)
    (hD : s 243 = List.replicate D true)
    (hzero : s 104 = List.replicate (4 * baseWidth p (D + 1)) false)
    (hempty : ∀ i ∈ SubexpLocalCRTFrames.scratch, s i = []) :
    SubexpLocalSeedProgram.Ready p (D + 1) M
      (SubexpLocalInitializedScan.output p D M s t z theta one minusOne nodes index O)
      D ((tail.map SubexpFlatAdd.encode).flatten) t a one minusOne width width := by
  have hframe (j : Fin 256) (hj : j ∉ SubexpLocalInitializedScan.changed) :=
    SubexpLocalInitializedScan.output_frame p D M s t z theta one minusOne nodes index O
      (hempty 218 (by decide)) (hempty 219 (by decide)) j hj
  constructor
  · exact hw
  · exact hw
  · intro i
    rw [hframe _ (not_changed_of_lt _ (SubexpLocalSeedProgram.native_below i))]
    exact hnative i
  · rw [hframe 207 (by decide)]
    exact hone
  · intro i
    rw [hframe _ (by fin_cases i <;> decide)]
    exact hneg i
  · rw [SubexpLocalInitializedScan.output_value]
    simp [encode, encodeArray, harray]
  · rw [hframe 243 (by decide)]
    exact hD
  · rw [hframe 104 (by decide)]
    exact hzero
  · intro j hj
    obtain ⟨hn, hs⟩ := seed_work_frame j hj
    rw [hframe j hn]
    exact hempty j hs

end SubexponentialSAT.SubexpLocalReadiness

end OAI.Algorithms
