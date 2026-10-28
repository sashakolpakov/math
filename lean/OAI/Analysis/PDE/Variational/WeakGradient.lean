import OAI.Analysis.PDE.Variational.Tests

open Set _root_.MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section

namespace OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem cell_integration_by_parts (a b : CellCoordinates m) (hab : a ≤ b)
    (j : Fin (m+1)) {u φ : CellCoordinates m → ℝ}
    (hu : ContDiff ℝ 1 u) (hφ : ContDiff ℝ 1 φ)
    (hface : ∀ y ∈ Icc (a ∘ j.succAbove) (b ∘ j.succAbove),
      φ (j.insertNth (a j) y) = 0 ∧ φ (j.insertNth (b j) y) = 0) :
    (∫ x in Icc a b, fderiv ℝ φ x (Pi.single j 1) * u x) =
      -(∫ x in Icc a b, φ x * fderiv ℝ u x (Pi.single j 1)) := by
  let F : Fin (m+1) → CellCoordinates m → ℝ := fun i x ↦ if i=j then u x else 0
  have hF : ∀ i, ContDiff ℝ 1 (F i) := by
    intro i
    by_cases hi : i=j
    · simpa [F, hi] using hu
    · simpa [F, hi] using (contDiff_const : ContDiff ℝ 1 (fun _ : CellCoordinates m ↦ (0:ℝ)))
  have h := OAI.Analysis.PDE.Green.integral_product_divergence_box a b hab F hF hφ (by
    intro i y hy
    by_cases hi : i=j
    · subst i
      simp [(hface y hy).1, (hface y hy).2]
    · simp [F, hi])
  have hd (x : CellCoordinates m) :
      (∑ i, fderiv ℝ (F i) x (Pi.single i 1)) = fderiv ℝ u x (Pi.single j 1) := by
    rw [Finset.sum_eq_single j]
    · simp [F]
    · intro i _ hi
      simp [F, hi]
    · simp
  simp_rw [hd] at h
  have hf (x : CellCoordinates m) :
      (∑ i, fderiv ℝ φ x (Pi.single i 1) * F i x) =
        fderiv ℝ φ x (Pi.single j 1) * u x := by simp [F]
  simp_rw [hf] at h
  linarith

theorem inner_cellToL2_left {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b : CellCoordinates m) (f : CellCoordinates m → H) (hf : Continuous f)
    (g : Lp H 2 (volume.restrict (Icc a b))) :
    inner ℝ (cellToL2 a b f hf) g = ∫ x in Icc a b, inner ℝ (f x) (g x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_continuous_cell a b hf).coeFn_toLp] with x hx
  simp only [cellToL2]
  rw [hx]

theorem inner_cellToL2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b : CellCoordinates m) (f g : CellCoordinates m → H)
    (hf : Continuous f) (hg : Continuous g) :
    inner ℝ (cellToL2 a b f hf) (cellToL2 a b g hg) =
      ∫ x in Icc a b, inner ℝ (f x) (g x) := by
  rw [inner_cellToL2_left]
  apply integral_congr_ae
  filter_upwards [(memLp_continuous_cell a b hg).coeFn_toLp] with x hx
  simp only [cellToL2]
  rw [hx]

def coordinateTestVector (j : Fin (m+1)) (φ : CellCoordinates m → ℝ)
    (x : CellCoordinates m) : CellVectors m := φ x • EuclideanSpace.single j 1

theorem continuous_coordinateTestVector (j : Fin (m+1)) {φ : CellCoordinates m → ℝ}
    (hφ : Continuous φ) : Continuous (coordinateTestVector j φ) :=
  hφ.smul continuous_const

@[simp] theorem inner_coordinateTestVector (j : Fin (m+1)) (φ : CellCoordinates m → ℝ)
    (x : CellCoordinates m) (v : CellVectors m) :
    inner ℝ (coordinateTestVector j φ x) v = φ x * v j := by
  rw [coordinateTestVector, real_inner_smul_left]
  simp [EuclideanSpace.inner_single_left]

/-- Genuine distributional gradient identity for the L² function represented by an
element of the completed energy space. Only the scalar test vanishes at the chosen
cell faces; the completed solution remains periodic in the period directions. -/
theorem periodicValue_weak_derivative (a b : CellCoordinates m) (hab : a ≤ b)
    (Ω P : Set (CellCoordinates m)) (k : Fin (m+1))
    (hΩ : ∀ y ∈ Icc (a ∘ k.succAbove) (b ∘ k.succAbove), k.insertNth (b k) y ∉ Ω)
    (u : PeriodicH10 a b Ω P) (j : Fin (m+1)) {φ : CellCoordinates m → ℝ}
    (hφ : ContDiff ℝ 1 φ)
    (hface : ∀ y ∈ Icc (a ∘ j.succAbove) (b ∘ j.succAbove),
      φ (j.insertNth (a j) y) = 0 ∧ φ (j.insertNth (b j) y) = 0) :
    (∫ x in Icc a b, fderiv ℝ φ x (Pi.single j 1) * periodicValue a b Ω P u x) =
      -(∫ x in Icc a b, φ x * (u.val x) j) := by
  let dφ := cellToL2 a b (fun x ↦ fderiv ℝ φ x (Pi.single j 1))
    (OAI.Analysis.PDE.Green.continuous_directional hφ (Pi.single j 1))
  let vφ := cellToL2 a b (coordinateTestVector j φ)
    (continuous_coordinateTestVector j hφ.continuous)
  have htest (v : PeriodicTests Ω P) :
      inner ℝ dφ (testValueMap a b Ω P v) = -inner ℝ vφ (testGradientMap a b Ω P v) := by
    change inner ℝ dφ (cellToL2 a b (v : CellCoordinates m → ℝ)
      (periodicTest_contDiff v).continuous) =
      -inner ℝ vφ (cellToL2 a b (cellGradient v)
        (continuous_cellGradient (periodicTest_contDiff_one v)))
    dsimp [dφ, vφ]
    rw [inner_cellToL2, inner_cellToL2]
    simp only [inner_coordinateTestVector, cellGradient_apply,
      RCLike.inner_apply, conj_trivial]
    simpa only [mul_comm] using cell_integration_by_parts a b hab j
      (periodicTest_contDiff_one v) hφ hface
  have h := completedValue_pairing (testGradientMap a b Ω P) (testValueMap a b Ω P)
    (testValueMap_poincare a b hab Ω P k hΩ) (innerSL ℝ dφ) (-(innerSL ℝ vφ)) htest u
  change inner ℝ dφ (periodicValue a b Ω P u) = -inner ℝ vφ u.val at h
  dsimp [dφ, vφ] at h
  rw [inner_cellToL2_left, inner_cellToL2_left] at h
  simpa only [inner_coordinateTestVector, RCLike.inner_apply, conj_trivial, mul_comm] using h

end OAI.Analysis.PDE.Variational
