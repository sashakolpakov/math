import OAI.Analysis.PDE.Green.Localized.Flux
import OAI.Analysis.PDE.Green.WeightedCoordinates
import OAI.Analysis.PDE.Green.EuclideanCell

/-! Coordinate transport of the localized quantitative divergence estimate. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory

theorem coordinate_weighted_divergence_of_normal_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] {m : ℕ}
    (e : E ≃L[ℝ] (Fin (m + 1) → ℝ)) (he : MeasurePreserving e)
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : Fin (m + 1) → E → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r v : E → ℝ} (hr : ContDiff ℝ 1 r) (hv : Continuous v)
    {ε W C : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ k : ℕ, (∫ x in e ⁻¹' Icc a b, normalCutoffWeight (r x) k * ‖v x‖) ≤ W)
    (hbound : ∀ x ∈ e ⁻¹' Icc a b,
      ‖∑ i, fderiv ℝ r x (e.symm (Pi.single i 1)) * F i x‖ ≤ ε * ‖v x‖ + C * ‖r x‖)
    (hface : CompatibleBoxFaces a b (fun y => r (e.symm y)) (fun i y => F i (e.symm y))) :
    ‖∫ x in (e ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∑ i, fderiv ℝ (F i) x (e.symm (Pi.single i 1))‖ ≤ ε * W := by
  have hc : ContDiff ℝ 1 (fun y => r (e.symm y)) := hr.comp e.symm.contDiff
  have hfc : ∀ i, ContDiff ℝ 1 (fun y => F i (e.symm y)) :=
    fun i => (hF i).comp e.symm.contDiff
  have hdr (y w : Fin (m + 1) → ℝ) :
      fderiv ℝ (fun z => r (e.symm z)) y w = fderiv ℝ r (e.symm y) (e.symm w) := by
    simpa only using! fderiv_comp_linear_apply e.symm.toContinuousLinearMap hr y w
  have hdf (i) (y w : Fin (m + 1) → ℝ) :
      fderiv ℝ (fun z => F i (e.symm z)) y w = fderiv ℝ (F i) (e.symm y) (e.symm w) := by
    simpa only using! fderiv_comp_linear_apply e.symm.toContinuousLinearMap (hF i) y w
  have hweight (k : ℕ) : (∫ y in Icc a b,
      normalCutoffWeight (r (e.symm y)) k * ‖v (e.symm y)‖) ≤ W := by
    have hm := he.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding
      (fun y => normalCutoffWeight (r (e.symm y)) k * ‖v (e.symm y)‖) (Icc a b)
    rw [← hm]
    simpa only [e.symm_apply_apply] using hW k
  have hbound' (y : Fin (m + 1) → ℝ) (hy : y ∈ Icc a b) :
      ‖∑ i, fderiv ℝ (fun z => r (e.symm z)) y (Pi.single i 1) * F i (e.symm y)‖ ≤
        ε * ‖v (e.symm y)‖ + C * ‖r (e.symm y)‖ := by
    simpa only [hdr] using hbound (e.symm y) (by simpa using hy)
  have hz := weighted_small_divergence_of_normal_bound a b hab
    (fun i y => F i (e.symm y)) hfc hc (hv.comp e.symm.continuous) hε hweight hbound' hface
  simp_rw [hdf] at hz
  have hm := he.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding
    (fun y => ∑ i, fderiv ℝ (F i) (e.symm y) (e.symm (Pi.single i 1)))
    (Icc a b ∩ {y | r (e.symm y) < 0})
  have hEq : (∫ x in (e ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∑ i, fderiv ℝ (F i) x (e.symm (Pi.single i 1))) =
      ∫ y in Icc a b ∩ {y | r (e.symm y) < 0},
        ∑ i, fderiv ℝ (F i) (e.symm y) (e.symm (Pi.single i 1)) := by
    simpa only [Set.preimage_inter, Set.preimage_ofPred_eq, e.symm_apply_apply] using hm
  rw [hEq]
  exact hz

theorem euclidean_weighted_divergence_of_normal_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : ι → EuclideanSpace ℝ ι → ℝ) (hF : ∀ i, ContDiff ℝ 1 (F i))
    {r v : EuclideanSpace ℝ ι → ℝ} (hr : ContDiff ℝ 1 r) (hv : Continuous v)
    {ε W C : ℝ} (hε : 0 ≤ ε)
    (hW : ∀ k : ℕ, (∫ x in euclideanCoordinates c ⁻¹' Icc a b,
      normalCutoffWeight (r x) k * ‖v x‖) ≤ W)
    (hbound : ∀ x ∈ euclideanCoordinates c ⁻¹' Icc a b,
      ‖∑ i, fderiv ℝ r x (EuclideanSpace.single i 1) * F i x‖ ≤ ε * ‖v x‖ + C * ‖r x‖)
    (hface : CompatibleCellFaces c a b r F) :
    ‖∫ x in (euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∑ i, fderiv ℝ (F i) x (EuclideanSpace.single i 1)‖ ≤ ε * W := by
  have hbound' (x : EuclideanSpace ℝ ι) (hx : x ∈ euclideanCoordinates c ⁻¹' Icc a b) :
      ‖∑ i, fderiv ℝ r x ((euclideanCoordinates c).symm (Pi.single i 1)) * F (c.symm i) x‖ ≤
        ε * ‖v x‖ + C * ‖r x‖ := by
    simp only [euclideanCoordinates_symm_single]
    rw [c.symm.sum_comp (fun j => fderiv ℝ r x (EuclideanSpace.single j 1) * F j x)]
    exact hbound x hx
  have hz := coordinate_weighted_divergence_of_normal_bound (euclideanCoordinates c)
    (measurePreserving_euclideanCoordinates c) a b hab (fun i => F (c.symm i))
    (fun i => hF (c.symm i)) hr hv hε hW hbound' hface
  have hsum (x : EuclideanSpace ℝ ι) :=
    c.symm.sum_comp (fun j => fderiv ℝ (F j) x (EuclideanSpace.single j 1))
  simpa only [euclideanCoordinates_symm_single, hsum] using hz

end OAI.Analysis.PDE.Green
