import OAI.Analysis.PDE.Green.CellGreen
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Periodic cells in Euclidean spaces with an arbitrary finite coordinate index. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory
open scoped Topology

def euclideanCoordinates {ι : Type*} [Fintype ι] {m : ℕ} (c : ι ≃ Fin (m + 1)) :
    EuclideanSpace ℝ ι ≃L[ℝ] (Fin (m + 1) → ℝ) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).trans
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin (m + 1) => ℝ) c)

theorem measurePreserving_euclideanCoordinates {ι : Type*} [Fintype ι] {m : ℕ}
    (c : ι ≃ Fin (m + 1)) : MeasurePreserving (euclideanCoordinates c) := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : Fin (m + 1) => ℝ) c).comp
    (PiLp.volume_preserving_ofLp ι)
  simpa only [euclideanCoordinates] using! h

theorem euclideanCoordinates_symm_single {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (c : ι ≃ Fin (m + 1)) (i : Fin (m + 1)) :
    (euclideanCoordinates c).symm (Pi.single i 1) = EuclideanSpace.single (c.symm i) 1 := by
  ext j
  change ((Pi.single i (1 : ℝ)) : Fin (m + 1) → ℝ) (c j) =
    ((Pi.single (c.symm i) (1 : ℝ)) : ι → ℝ) j
  by_cases hj : j = c.symm i
  · subst j
    simp
  · have hcj : c j ≠ i := by
      intro hh
      apply hj
      exact c.injective (hh.trans (c.apply_symm_apply i).symm)
    simp [hj, hcj]

theorem integral_divergence_euclidean_cell_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : ι → EuclideanSpace ℝ ι → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r : EuclideanSpace ℝ ι → ℝ} (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (hzero : ∀ x, r x = 0 →
      ∑ i, fderiv ℝ r x (EuclideanSpace.single i 1) * F i x = 0)
    (hface : ∀ i, ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      (r ((euclideanCoordinates c).symm (i.insertNth (b i) y)) =
          r ((euclideanCoordinates c).symm (i.insertNth (a i) y)) ∧
        F (c.symm i) ((euclideanCoordinates c).symm (i.insertNth (b i) y)) =
          F (c.symm i) ((euclideanCoordinates c).symm (i.insertNth (a i) y))) ∨
      (0 ≤ r ((euclideanCoordinates c).symm (i.insertNth (b i) y)) ∧
        0 ≤ r ((euclideanCoordinates c).symm (i.insertNth (a i) y))) ∨
      (F (c.symm i) ((euclideanCoordinates c).symm (i.insertNth (b i) y)) = 0 ∧
        F (c.symm i) ((euclideanCoordinates c).symm (i.insertNth (a i) y)) = 0)) :
    (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1)) = 0 := by
  have hzero' : ∀ x, r x = 0 → ∑ i : Fin (m + 1),
      fderiv ℝ r x ((euclideanCoordinates c).symm (Pi.single i 1)) * F (c.symm i) x = 0 := by
    intro x hx
    simp only [euclideanCoordinates_symm_single]
    rw [c.symm.sum_comp (fun j => fderiv ℝ r x (EuclideanSpace.single j 1) * F j x)]
    exact hzero x hx
  have hz := integral_divergence_coordinate_cell_zero (euclideanCoordinates c)
    (measurePreserving_euclideanCoordinates c) a b hab (fun i => F (c.symm i))
    (fun i => hF (c.symm i)) hr hrne hzero' hface
  have hsum (x : EuclideanSpace ℝ ι) :=
    c.symm.sum_comp (fun j => fderiv ℝ (F j) x (EuclideanSpace.single j 1))
  simpa only [euclideanCoordinates_symm_single, hsum] using hz

def CompatibleCellFaces {ι : Type*} [Fintype ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (a b : Fin (m + 1) → ℝ) (r : EuclideanSpace ℝ ι → ℝ)
    (F : ι → EuclideanSpace ℝ ι → ℝ) : Prop :=
  ∀ i, ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
    (r ((euclideanCoordinates c).symm (i.insertNth (b i) y)) =
        r ((euclideanCoordinates c).symm (i.insertNth (a i) y)) ∧
      F (c.symm i) ((euclideanCoordinates c).symm (i.insertNth (b i) y)) =
        F (c.symm i) ((euclideanCoordinates c).symm (i.insertNth (a i) y))) ∨
    (0 ≤ r ((euclideanCoordinates c).symm (i.insertNth (b i) y)) ∧
      0 ≤ r ((euclideanCoordinates c).symm (i.insertNth (a i) y))) ∨
    (F (c.symm i) ((euclideanCoordinates c).symm (i.insertNth (b i) y)) = 0 ∧
      F (c.symm i) ((euclideanCoordinates c).symm (i.insertNth (a i) y)) = 0)

theorem isBounded_euclidean_cell {ι : Type*} [Fintype ι] {m : ℕ}
    (c : ι ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ) :
    Bornology.IsBounded (euclideanCoordinates c ⁻¹' Icc a b) := by
  apply (isCompact_Icc.image (euclideanCoordinates c).symm.continuous).isBounded.subset
  intro x hx
  exact ⟨euclideanCoordinates c x, hx, (euclideanCoordinates c).symm_apply_apply x⟩

/-- Second Green identity on a periodic cell intersected with a regular sublevel.
The full sublevel can be unbounded, as in the periodic geometry of the source. -/
theorem real_operator_second_green_cell
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (K : ι → ι → EuclideanSpace ℝ ι → ℝ) {r u v : EuclideanSpace ℝ ι → ℝ}
    (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hKs : ∀ i j x, K i j x = K j i x)
    (hdiv : ∀ x j, ∑ i, fderiv ℝ (K i j) x (EuclideanSpace.single i 1) = 0)
    (hrne : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hnormal : ∀ x, r x = 0 →
      (∑ i, ∑ j, K i j x * (fderiv ℝ r x (EuclideanSpace.single i 1) *
        fderiv ℝ r x (EuclideanSpace.single j 1))) = 0)
    (hface : CompatibleCellFaces c a b r
      (secondGreenFlux (fun i => EuclideanSpace.single i 1) K u v)) :
    (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, u x *
      (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) =
    ∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, v x *
      (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) := by
  let d : ι → EuclideanSpace ℝ ι := fun i => EuclideanSpace.single i 1
  have hb := (isBounded_euclidean_cell c a b).subset
    (inter_subset_left : ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) ⊆ _)
  have hvF := contDiff_realFlux d K hK hv
  have huF := contDiff_realFlux d K hK hu
  have hvi : IntegrableOn (fun x => u x * ∑ i, fderiv ℝ (realFlux d K v i) x (d i))
      ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hu.continuous.mul
      (continuous_finsetSum _ (fun i _ => continuous_directional (hvF i) (d i))))
  have hui : IntegrableOn (fun x => v x * ∑ i, fderiv ℝ (realFlux d K u i) x (d i))
      ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hv.continuous.mul
      (continuous_finsetSum _ (fun i _ => continuous_directional (huF i) (d i))))
  have he := integral_divergence_euclidean_cell_zero c a b hab (secondGreenFlux d K u v)
    (contDiff_secondGreenFlux d K hK hu hv) hr hrne
    (secondGreenFlux_tangent d K hr hu huz hnormal) hface
  change (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
    ∑ i, fderiv ℝ (secondGreenFlux d K u v i) x (d i)) = 0 at he
  simp_rw [secondGreenFlux_divergence d K hK hu hv hKs] at he
  rw [integral_sub hvi hui] at he
  have heq := sub_eq_zero.mp he
  simpa only [realFlux_divergence d K hK hv hdiv,
    realFlux_divergence d K hK hu hdiv] using heq

end OAI.Analysis.PDE.Green
