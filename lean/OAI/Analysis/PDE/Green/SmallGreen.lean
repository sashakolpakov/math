import OAI.Analysis.PDE.Green.WeightedCoordinates
import OAI.Analysis.PDE.Green.EuclideanCell

/-! The quantitative second Green identity on periodic cells. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory

theorem euclidean_weighted_small_divergence_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : ι → EuclideanSpace ℝ ι → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r q₀ q₁ v : EuclideanSpace ℝ ι → ℝ} (hr : ContDiff ℝ 2 r)
    (hq₀ : ContDiff ℝ 1 q₀) (hq₁ : ContDiff ℝ 1 q₁) (hv : Continuous v)
    (hrne : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    {ε W : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ k : ℕ, (∫ x in euclideanCoordinates c ⁻¹' Icc a b,
      normalCutoffWeight (r x) k * ‖v x‖) ≤ W)
    (hzero : ∀ x, r x = 0 → q₁ x = 0)
    (hbound : ∀ x, r x = 0 → ‖q₀ x‖ ≤ ε)
    (hdecomp : ∀ x, (∑ i, fderiv ℝ r x (EuclideanSpace.single i 1) * F i x) =
      v x * q₀ x + q₁ x)
    (hface : CompatibleCellFaces c a b r F) :
    ‖∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1)‖ ≤ ε * W := by
  have hdec (x : EuclideanSpace ℝ ι) :
      (∑ i, fderiv ℝ r x ((euclideanCoordinates c).symm (Pi.single i 1)) * F (c.symm i) x) =
        v x * q₀ x + q₁ x := by
    simp only [euclideanCoordinates_symm_single]
    rw [c.symm.sum_comp (fun j => fderiv ℝ r x (EuclideanSpace.single j 1) * F j x)]
    exact hdecomp x
  have hz := coordinate_weighted_small_divergence_bound (euclideanCoordinates c)
    (measurePreserving_euclideanCoordinates c) a b hab (fun i => F (c.symm i))
    (fun i => hF (c.symm i)) hr hq₀ hq₁ hv hrne hε hW hzero hbound hdec hface
  have hsum (x : EuclideanSpace ℝ ι) :=
    c.symm.sum_comp (fun j => fderiv ℝ (F j) x (EuclideanSpace.single j 1))
  simpa only [euclideanCoordinates_symm_single, hsum] using hz

section NormalFlux
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

def normalRealFlux (d : ι → E) (K : ι → ι → E → ℝ) (r u : E → ℝ) (x : E) : ℝ :=
  ∑ i, fderiv ℝ r x (d i) * realFlux d K u i x

theorem contDiff_normalRealFlux (d : ι → E) (K : ι → ι → E → ℝ)
    {r u : E → ℝ} (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (normalRealFlux d K r u) :=
  ContDiff.sum (fun i _ =>
    ((hr.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).mul
      (contDiff_realFlux d K hK hu i))

theorem secondGreenFlux_normal_decomposition (d : ι → E) (K : ι → ι → E → ℝ)
    (r u v : E → ℝ) (x : E) :
    (∑ i, fderiv ℝ r x (d i) * secondGreenFlux d K u v i x) =
      v x * (-normalRealFlux d K r u x) + u x * normalRealFlux d K r v x := by
  calc
    _ = u x * normalRealFlux d K r v x - v x * normalRealFlux d K r u x := by
      simp only [normalRealFlux, secondGreenFlux, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by ring

end NormalFlux

/-- The only boundary input is the small conormal derivative of `u`; derivatives
of the test `v` do not occur in the error bound. -/
theorem real_operator_second_green_cell_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (K : ι → ι → EuclideanSpace ℝ ι → ℝ) {r u v : EuclideanSpace ℝ ι → ℝ}
    (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hKs : ∀ i j x, K i j x = K j i x)
    (hdiv : ∀ x j, ∑ i, fderiv ℝ (K i j) x (EuclideanSpace.single i 1) = 0)
    (hrne : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    {ε W : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ k : ℕ, (∫ x in euclideanCoordinates c ⁻¹' Icc a b,
      normalCutoffWeight (r x) k * ‖v x‖) ≤ W)
    (hnormal : ∀ x, r x = 0 →
      ‖normalRealFlux (fun i => EuclideanSpace.single i 1) K r u x‖ ≤ ε)
    (hface : CompatibleCellFaces c a b r
      (secondGreenFlux (fun i => EuclideanSpace.single i 1) K u v)) :
    ‖(∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, u x *
      (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ v) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) -
    ∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, v x *
      (∑ i, ∑ j, K i j x * fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))‖ ≤ ε * W := by
  let d : ι → EuclideanSpace ℝ ι := fun i => EuclideanSpace.single i 1
  have hq₀ : ContDiff ℝ 1 (fun x => -normalRealFlux d K r u x) :=
    (contDiff_normalRealFlux d K hK hr hu).neg
  have hq₁ : ContDiff ℝ 1 (fun x => u x * normalRealFlux d K r v x) :=
    (hu.of_le (by norm_num)).mul (contDiff_normalRealFlux d K hK hr hv)
  have he := euclidean_weighted_small_divergence_bound c a b hab (secondGreenFlux d K u v)
    (contDiff_secondGreenFlux d K hK hu hv) hr hq₀ hq₁ hv.continuous hrne hε hW
    (by intro x hx; rw [huz x hx, zero_mul])
    (by intro x hx; simpa only [norm_neg] using hnormal x hx)
    (secondGreenFlux_normal_decomposition d K r u v) hface
  have hb := (isBounded_euclidean_cell c a b).subset
    (inter_subset_left : ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) ⊆ _)
  have hvi : IntegrableOn (fun x => u x * ∑ i, fderiv ℝ (realFlux d K v i) x (d i))
      ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hu.continuous.mul
      (continuous_finsetSum _ (fun i _ => continuous_directional (contDiff_realFlux d K hK hv i) (d i))))
  have hui : IntegrableOn (fun x => v x * ∑ i, fderiv ℝ (realFlux d K u i) x (d i))
      ((euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) :=
    OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (hv.continuous.mul
      (continuous_finsetSum _ (fun i _ => continuous_directional (contDiff_realFlux d K hK hu i) (d i))))
  change ‖∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
    ∑ i, fderiv ℝ (secondGreenFlux d K u v i) x (d i)‖ ≤ ε * W at he
  simp_rw [secondGreenFlux_divergence d K hK hu hv hKs] at he
  rw [integral_sub hvi hui] at he
  simpa only [realFlux_divergence d K hK hv hdiv,
    realFlux_divergence d K hK hu hdiv] using he

end OAI.Analysis.PDE.Green
