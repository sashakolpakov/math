import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLocalCRTSetup
import OAI.Algorithms.SubexponentialSAT.SubexpLocalProductScan

namespace OAI.Algorithms

/-! Physical cache initialization followed by the concrete node scan. The
arithmetic readiness condition is a finite description of stored metadata
and empty work cells, not an assumed execution of the scan. -/

namespace SubexponentialSAT.SubexpLocalInitializedScan

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing SubexpPolynomialPowerProgram

def command : Code := .seq SubexpLocalCRTSetup.initializeCaches
  (SubexpNodeScanControl.command SubexpLocalProductProgram.command)

def workPorts : List (Fin 256) :=
  [100,101,102,107,108,120,215,217,218,219,220,229,240,242,245]

theorem work_eq {A C : Type*} (s : Store) (encodeC : C → List Bool) (encodeA : A → List Bool)
    (cs : List C) (x : SubexpNodeScanControl.Cursor A) (current negative : List Bool)
    (h : ∀ i, s (SubexpNodeScanControl.ports i) =
      SubexpNodeScanControl.words encodeC encodeA cs x current negative i) :
    SubexpNodeScanControl.ready s encodeC encodeA cs x current negative = s := by
  classical
  funext j
  by_cases hj : ∃ i, SubexpNodeScanControl.ports i = j
  · obtain ⟨i, rfl⟩ := hj
    rw [SubexpNodeScanControl.ready, SubexpNodeScanControl.work_port, h]
  · exact SubexpNodeScanControl.work_frame s _ j hj

variable (p D : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p (D + 1))

abbrev Coeff := Coefficient p (D + 1)
abbrev Poly := FixedPolynomial p (D + 1) D

def initial (s : Store) : Store :=
  SubexpLocalCRTSetup.initialized s D (baseWidth p (D + 1))

noncomputable def output (s : Store) (t z theta one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (nodes : List (Coeff p D))
    (index : List Bool) (O : Poly p D) : Store :=
  SubexpNodeScanControl.ready (initial p D s) SubexpFlatAdd.encode (encode p (D + 1)) ([] : List (Coeff p D))
    (SubexpNodeScanControl.run (SubexpLocalProductScan.stepValue p D M t z theta one minusOne)
      nodes ⟨O, index, true⟩) [] []

def changed : List (Fin 256) := [215,217,229,240,220,242]

omit [Fact p.Prime] in
theorem initial_frame (s : Store) (j : Fin 256) (hj : j ∉ changed) :
    initial p D s j = s j := by
  simp only [changed, List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
  rcases hj with ⟨h215, h217, h229, h240, h220, h242⟩
  simp [initial, SubexpLocalCRTSetup.initialized, h215, h217, h229, h240, h220, h242]

theorem output_frame (s : Store) (t z theta one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (nodes : List (Coeff p D))
    (index : List Bool) (O : Poly p D) (h218 : s 218 = []) (h219 : s 219 = [])
    (j : Fin 256) (hj : j ∉ changed) :
    output p D M s t z theta one minusOne nodes index O j = s j := by
  by_cases h218' : j = 218
  · subst j
    simp [output, SubexpNodeScanControl.ready, SubexpNodeScanControl.words, h218]
  · by_cases h219' : j = 219
    · subst j
      simp [output, SubexpNodeScanControl.ready, SubexpNodeScanControl.words, h219]
    · unfold output SubexpNodeScanControl.ready
      rw [SubexpNodeScanControl.work_frame]
      · exact initial_frame p D s j hj
      · rintro ⟨i, hi⟩
        fin_cases i
        · exact hj (by simp [changed, ← hi, SubexpNodeScanControl.ports])
        · exact hj (by simp [changed, ← hi, SubexpNodeScanControl.ports])
        · exact hj (by simp [changed, ← hi, SubexpNodeScanControl.ports])
        · exact hj (by simp [changed, ← hi, SubexpNodeScanControl.ports])
        · exact h218' hi.symm
        · exact h219' hi.symm

@[simp] theorem output_value (s : Store) (t z theta one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (nodes : List (Coeff p D))
    (index : List Bool) (O : Poly p D) :
    output p D M s t z theta one minusOne nodes index O 240 =
      encode p (D + 1) (SubexpNodeScanControl.run
        (SubexpLocalProductScan.stepValue p D M t z theta one minusOne)
        nodes ⟨O, index, true⟩).value := by
  simp [output, SubexpNodeScanControl.ready, SubexpNodeScanControl.words]

@[simp] theorem output_one (s : Store) (t z theta one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (nodes : List (Coeff p D))
    (index : List Bool) (O : Poly p D) :
    output p D M s t z theta one minusOne nodes index O 220 =
      SubexpLocalCRTSetup.oneArray D (baseWidth p (D + 1)) (s 207) := by
  unfold output SubexpNodeScanControl.ready
  rw [SubexpNodeScanControl.work_frame _ _ _ (by decide)]
  simp [initial, SubexpLocalCRTSetup.initialized]

@[simp] theorem output_zero (s : Store) (t z theta one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (nodes : List (Coeff p D))
    (index : List Bool) (O : Poly p D) :
    output p D M s t z theta one minusOne nodes index O 242 =
      SubexpLocalCRTSetup.zeroArray D (baseWidth p (D + 1)) := by
  unfold output SubexpNodeScanControl.ready
  rw [SubexpNodeScanControl.work_frame _ _ _ (by decide)]
  simp [initial, SubexpLocalCRTSetup.initialized]

theorem command_value (s : Store) (t z theta one : Coeff p D)
    (minusOne : Word (baseWidth p (D + 1))) (width : List Bool) (frame : Fin 6 → List Bool)
    (nodes : List (Coeff p D)) (index : List Bool) (O : Poly p D)
    (H : SubexpLocalProductScan.Ready p D M (initial p D s) t z theta one minusOne width frame)
    (hD : s 243 = List.replicate D true)
    (hzero : s 104 = List.replicate (4 * baseWidth p (D + 1)) false)
    (hone : (s 207).length = 4 * baseWidth p (D + 1))
    (hO : SubexpLocalCRTSetup.oneArray D (baseWidth p (D + 1)) (s 207) = encode p (D + 1) O)
    (hnodes : s 214 = nodes.flatMap SubexpFlatAdd.encode) (hindex : s 216 = index)
    (hempty : ∀ j ∈ workPorts, s j = []) :
    ExecutesIn command
      (500 * (D + 1) * (baseWidth p (D + 1) + 1) +
        7 * ((s 214).length + index.length) + 20 +
        (nodes.length * (700000 * (D + 1)^4 * (baseWidth p (D + 1) + 1)^2 +
          18 * (4 * baseWidth p (D + 1)) + 28) + 2))
      s (output p D M s t z theta one minusOne nodes index O) := by
  have h₁ := SubexpLocalCRTSetup.initialize_run s D (baseWidth p (D + 1))
    hD hzero hone (hempty 100 (by decide)) (hempty 101 (by decide))
    (hempty 102 (by decide)) (hempty 107 (by decide)) (hempty 108 (by decide))
    (hempty 120 (by decide)) (hempty 215 (by decide)) (hempty 217 (by decide))
    (hempty 220 (by decide)) (hempty 229 (by decide)) (hempty 240 (by decide))
    (hempty 242 (by decide)) (hempty 245 (by decide))
  have hstart : SubexpNodeScanControl.ready (initial p D s) SubexpFlatAdd.encode
      (encode p (D + 1)) nodes ⟨O, index, true⟩ [] [] = initial p D s := by
    apply work_eq
    intro i
    fin_cases i <;>
      simp [initial, SubexpLocalCRTSetup.initialized, SubexpNodeScanControl.ports,
        SubexpNodeScanControl.words, SubexpNodeScanControl.marker, hO, hnodes, hindex,
        hempty 218 (by decide), hempty 219 (by decide)]
  have h₂ := SubexpLocalProductScan.command_value p D M (initial p D s)
    t z theta one minusOne width frame H nodes ⟨O, index, true⟩
  rw [hstart] at h₂
  simpa only [command, output, hindex] using h₁.seq h₂

end SubexponentialSAT.SubexpLocalInitializedScan

end OAI.Algorithms
