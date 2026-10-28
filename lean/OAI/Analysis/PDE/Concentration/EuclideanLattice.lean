import OAI.Analysis.PDE.Concentration.Lattice.Faces
import OAI.Analysis.PDE.Green.EuclideanCell

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.PDE.Green

def euclideanLatticeCell {ι : Type*} [Fintype ι] {m : ℕ}
    (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) : Set (EuclideanSpace ℝ ι) :=
  OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' (L '' Icc a b)

def latticeCoordinateField {ι : Type*} [Fintype ι] {m : ℕ}
    (c : ι ≃ Fin (m + 1)) (F : ι → EuclideanSpace ℝ ι → ℝ)
    (y : Fin (m + 1) → ℝ) (i : Fin (m + 1)) : ℝ :=
  F (c.symm i) ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm y)

def CompatibleLatticeFaces {ι : Type*} [Fintype ι] {m : ℕ}
    (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (r : EuclideanSpace ℝ ι → ℝ)
    (F : ι → EuclideanSpace ℝ ι → ℝ) : Prop :=
  ∀ i, ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
    (r ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L (i.insertNth (b i) y))) =
        r ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L (i.insertNth (a i) y))) ∧
      linearPiola L (latticeCoordinateField c F) (i.insertNth (b i) y) i =
        linearPiola L (latticeCoordinateField c F) (i.insertNth (a i) y) i) ∨
    (0 ≤ r ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L (i.insertNth (b i) y))) ∧
      0 ≤ r ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L (i.insertNth (a i) y)))) ∨
    (linearPiola L (latticeCoordinateField c F) (i.insertNth (b i) y) i = 0 ∧
      linearPiola L (latticeCoordinateField c F) (i.insertNth (a i) y) i = 0)

theorem measurableSet_euclideanLatticeCell {ι : Type*} [Fintype ι] {m : ℕ}
    (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) : MeasurableSet (euclideanLatticeCell c L a b) :=
  ((isCompact_Icc.image L.continuous).isClosed.preimage
    (OAI.Analysis.PDE.Green.euclideanCoordinates c).continuous).measurableSet

theorem isBounded_euclideanLatticeCell {ι : Type*} [Fintype ι] {m : ℕ}
    (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) : Bornology.IsBounded (euclideanLatticeCell c L a b) := by
  apply ((isCompact_Icc.image L.continuous).image
    (OAI.Analysis.PDE.Green.euclideanCoordinates c).symm.continuous).isBounded.subset
  intro x hx
  exact ⟨OAI.Analysis.PDE.Green.euclideanCoordinates c x, hx, (OAI.Analysis.PDE.Green.euclideanCoordinates c).symm_apply_apply x⟩

/-- Divergence in the original orthonormal coordinates integrates to zero on
an arbitrary lattice cell. The change of variables changes the face-normal
components, but does not change the differential operator being integrated. -/
theorem integral_divergence_euclidean_lattice_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : ι → EuclideanSpace ℝ ι → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r : EuclideanSpace ℝ ι → ℝ} (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (hzero : ∀ x, r x = 0 →
      ∑ i, fderiv ℝ r x (EuclideanSpace.single i 1) * F i x = 0)
    (hface : CompatibleLatticeFaces c L a b r F) :
    (∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0},
      ∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1)) = 0 := by
  let e := OAI.Analysis.PDE.Green.euclideanCoordinates c
  let G := latticeCoordinateField c F
  have hG : ContDiff ℝ 1 G := contDiff_pi.mpr (fun i => (hF (c.symm i)).comp e.symm.contDiff)
  have hdr (y v : Fin (m + 1) → ℝ) :
      fderiv ℝ (r ∘ e.symm) y v = fderiv ℝ r (e.symm y) (e.symm v) := by
    exact OAI.Analysis.PDE.Green.fderiv_comp_linear_apply e.symm.toContinuousLinearMap (hr.of_le (by norm_num)) y v
  have hdf (y : Fin (m + 1) → ℝ) : coordinateDivergence G y =
      ∑ i, fderiv ℝ (F i) (e.symm y) (EuclideanSpace.single i 1) := by
    rw [coordinateDivergence_eq_components (hG.differentiable (by norm_num) y)]
    have hi (i : Fin (m + 1)) : fderiv ℝ (fun z => G z i) y (Pi.single i 1) =
        fderiv ℝ (F (c.symm i)) (e.symm y) (EuclideanSpace.single (c.symm i) 1) := by
      change fderiv ℝ (fun z => F (c.symm i) (e.symm z)) y (Pi.single i 1) = _
      have heq : fderiv ℝ (fun z => F (c.symm i) (e.symm z)) y (Pi.single i 1) =
          fderiv ℝ (F (c.symm i)) (e.symm y) (e.symm (Pi.single i 1)) :=
        OAI.Analysis.PDE.Green.fderiv_comp_linear_apply e.symm.toContinuousLinearMap (hF (c.symm i)) y _
      rw [heq]
      exact congrArg (fderiv ℝ (F (c.symm i)) (e.symm y)) (OAI.Analysis.PDE.Green.euclideanCoordinates_symm_single c i)
    simp_rw [hi]
    exact c.symm.sum_comp (fun i => fderiv ℝ (F i) (e.symm y) (EuclideanSpace.single i 1))
  have hz := integral_divergence_parallelepiped_sublevel_zero L a b hab G hG
    (hr.comp e.symm.contDiff) (by
      intro y hy hyr heq
      apply hrne (e.symm y) (by simpa [euclideanLatticeCell, e] using hy) hyr
      ext v
      have hh := congrArg (fun D : (Fin (m + 1) → ℝ) →L[ℝ] ℝ => D (e v)) heq
      simpa only [hdr, e.symm_apply_apply, zero_apply] using hh)
    (by
      intro y hy
      change fderiv ℝ (r ∘ e.symm) y (G y) = 0
      rw [← sum_fderiv_coordinate_mul]
      simp_rw [hdr]
      have hs (i) : e.symm (Pi.single i 1) = EuclideanSpace.single (c.symm i) 1 :=
        OAI.Analysis.PDE.Green.euclideanCoordinates_symm_single c i
      simp_rw [hs]
      change (∑ i, fderiv ℝ r (e.symm y) (EuclideanSpace.single (c.symm i) 1) *
        F (c.symm i) (e.symm y)) = 0
      rw [c.symm.sum_comp (fun i => fderiv ℝ r (e.symm y) (EuclideanSpace.single i 1) *
        F i (e.symm y))]
      exact hzero _ hy) hface
  simp_rw [hdf] at hz
  have hz' : (∫ y in L '' Icc a b ∩ {y | r (e.symm y) < 0},
      ∑ i, fderiv ℝ (F i) (e.symm y) (EuclideanSpace.single i 1)) = 0 := by
    simpa only [Function.comp_def] using hz
  have hme : MeasurePreserving e := OAI.Analysis.PDE.Green.measurePreserving_euclideanCoordinates c
  have hm := hme.setIntegral_preimage_emb
    e.toHomeomorph.measurableEmbedding
    (fun y => ∑ i, fderiv ℝ (F i) (e.symm y) (EuclideanSpace.single i 1))
    (L '' Icc a b ∩ {y | r (e.symm y) < 0})
  have hfin := hm.trans hz'
  simpa only [euclideanLatticeCell, Set.preimage_inter, Set.preimage_ofPred_eq,
    e.symm_apply_apply] using hfin

end OAI.Analysis.PDE.Concentration
