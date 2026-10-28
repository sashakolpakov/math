import OAI.Analysis.PDE.Green.Localized.Divergence
import OAI.Analysis.PDE.Green.Periodicity

/-! Coordinate-invariant localized divergence and second Green identities. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory
open scoped Topology

theorem integral_divergence_coordinate_cell_localized
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] {m : ℕ}
    (e : E ≃L[ℝ] (Fin (m + 1) → ℝ)) (he : MeasurePreserving e)
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → E → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r : E → ℝ} (hr : ContDiff ℝ 2 r)
    (hreg : ∀ x ∈ e ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0 ∨
      ∀ᶠ y in 𝓝 x, ∀ i, F i y = 0)
    (hzero : ∀ x, r x = 0 →
      ∑ i, fderiv ℝ r x (e.symm (Pi.single i 1)) * F i x = 0)
    (hface : CompatibleBoxFaces a b (fun y => r (e.symm y)) (fun i y => F i (e.symm y))) :
    (∫ x in (e ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∑ i, fderiv ℝ (F i) x (e.symm (Pi.single i 1))) = 0 := by
  have hc : ContDiff ℝ 2 (fun y => r (e.symm y)) := hr.comp e.symm.contDiff
  have hfc : ∀ i, ContDiff ℝ 1 (fun y => F i (e.symm y)) :=
    fun i => (hF i).comp e.symm.contDiff
  have hdr (y v : Fin (m + 1) → ℝ) :
      fderiv ℝ (fun z => r (e.symm z)) y v = fderiv ℝ r (e.symm y) (e.symm v) := by
    simpa only using! fderiv_comp_linear_apply e.symm.toContinuousLinearMap
      (hr.of_le (by norm_num)) y v
  have hdf (i) (y v : Fin (m + 1) → ℝ) :
      fderiv ℝ (fun z => F i (e.symm z)) y v =
        fderiv ℝ (F i) (e.symm y) (e.symm v) := by
    simpa only using! fderiv_comp_linear_apply e.symm.toContinuousLinearMap (hF i) y v
  have hreg' : ∀ y ∈ Icc a b, r (e.symm y) = 0 →
      fderiv ℝ (fun z => r (e.symm z)) y ≠ 0 ∨
      ∀ᶠ z in 𝓝 y, ∀ i, F i (e.symm z) = 0 := by
    intro y hy hyr
    rcases hreg (e.symm y) (by simpa using hy) hyr with h | h
    · apply Or.inl
      intro hz
      apply h
      ext v
      have hh := congrArg (fun Q : (Fin (m + 1) → ℝ) →L[ℝ] ℝ => Q (e v)) hz
      simpa only [hdr, e.symm_apply_apply, zero_apply] using hh
    · exact Or.inr ((e.symm.continuous.tendsto y).eventually h)
  have htang : ∀ y, r (e.symm y) = 0 →
      ∑ i, fderiv ℝ (fun z => r (e.symm z)) y (Pi.single i 1) * F i (e.symm y) = 0 := by
    intro y hy
    simpa only [hdr] using hzero (e.symm y) hy
  have hz := integral_divergence_cell_localized a b hab
    (fun i y => F i (e.symm y)) hfc hc hreg' htang hface
  simp_rw [hdf] at hz
  have hm := he.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding
    (fun y => ∑ i, fderiv ℝ (F i) (e.symm y) (e.symm (Pi.single i 1)))
    (Icc a b ∩ {y | r (e.symm y) < 0})
  simpa only [Set.preimage_inter, Set.preimage_ofPred_eq, e.symm_apply_apply, hz] using hm

theorem integral_divergence_euclidean_cell_localized
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : ι → EuclideanSpace ℝ ι → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r : EuclideanSpace ℝ ι → ℝ} (hr : ContDiff ℝ 2 r)
    (hreg : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 →
      fderiv ℝ r x ≠ 0 ∨ ∀ᶠ y in 𝓝 x, ∀ i, F i y = 0)
    (hzero : ∀ x, r x = 0 →
      ∑ i, fderiv ℝ r x (EuclideanSpace.single i 1) * F i x = 0)
    (hface : CompatibleCellFaces c a b r F) :
    (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1)) = 0 := by
  have hzero' : ∀ x, r x = 0 → ∑ i : Fin (m + 1),
      fderiv ℝ r x ((euclideanCoordinates c).symm (Pi.single i 1)) * F (c.symm i) x = 0 := by
    intro x hx
    simp only [euclideanCoordinates_symm_single]
    rw [c.symm.sum_comp (fun j => fderiv ℝ r x (EuclideanSpace.single j 1) * F j x)]
    exact hzero x hx
  have hreg' : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 →
      fderiv ℝ r x ≠ 0 ∨ ∀ᶠ y in 𝓝 x, ∀ i, F (c.symm i) y = 0 := by
    intro x hx hrx
    rcases hreg x hx hrx with h | h
    · exact Or.inl h
    · exact Or.inr (h.mono (fun y hy i => hy (c.symm i)))
  have hz := integral_divergence_coordinate_cell_localized (euclideanCoordinates c)
    (measurePreserving_euclideanCoordinates c) a b hab (fun i => F (c.symm i))
    (fun i => hF (c.symm i)) hr hreg' hzero' hface
  have hsum (x : EuclideanSpace ℝ ι) :=
    c.symm.sum_comp (fun j => fderiv ℝ (F j) x (EuclideanSpace.single j 1))
  simpa only [euclideanCoordinates_symm_single, hsum] using hz

theorem secondGreenFlux_eventually_zero
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
    (d : I → E) (K : I → I → E → ℝ) (u v : E → ℝ) (x : E)
    (hv : v =ᶠ[𝓝 x] (fun _ => 0)) :
    ∀ᶠ y in 𝓝 x, ∀ i, secondGreenFlux d K u v i y = 0 := by
  have hloc : ∀ᶠ y in 𝓝 x, v =ᶠ[𝓝 y] (fun _ => 0) := eventually_eventually_nhds.mpr hv
  filter_upwards [hloc] with y hy i
  apply secondGreenFlux_zero_of_test_jet d K u v y hy.eq_of_nhds
  rw [hy.fderiv_eq]
  simp

theorem real_operator_second_green_cell_localized
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (K : ι → ι → EuclideanSpace ℝ ι → ℝ) {r u v : EuclideanSpace ℝ ι → ℝ}
    (hK : ∀ i j, ContDiff ℝ 1 (K i j))
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (hr : ContDiff ℝ 2 r)
    (hKs : ∀ i j x, K i j x = K j i x)
    (hdiv : ∀ x j, ∑ i, fderiv ℝ (K i j) x (EuclideanSpace.single i 1) = 0)
    (hreg : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 →
      fderiv ℝ r x ≠ 0 ∨ v =ᶠ[𝓝 x] (fun _ => 0))
    (hzero : ∀ x, r x = 0 → ∑ i, fderiv ℝ r x (EuclideanSpace.single i 1) *
      secondGreenFlux (fun i => EuclideanSpace.single i 1) K u v i x = 0)
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
  have hreg' : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b, r x = 0 →
      fderiv ℝ r x ≠ 0 ∨ ∀ᶠ y in 𝓝 x, ∀ i, secondGreenFlux d K u v i y = 0 := by
    intro x hx hrx
    rcases hreg x hx hrx with h | h
    · exact Or.inl h
    · exact Or.inr (secondGreenFlux_eventually_zero d K u v x h)
  have he := integral_divergence_euclidean_cell_localized c a b hab
    (secondGreenFlux d K u v) (contDiff_secondGreenFlux d K hK hu hv) hr hreg' hzero hface
  change (∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
    ∑ i, fderiv ℝ (secondGreenFlux d K u v i) x (d i)) = 0 at he
  simp_rw [secondGreenFlux_divergence d K hK hu hv hKs] at he
  rw [integral_sub hvi hui] at he
  have heq := sub_eq_zero.mp he
  simpa only [realFlux_divergence d K hK hv hdiv,
    realFlux_divergence d K hK hu hdiv] using heq

end OAI.Analysis.PDE.Green
