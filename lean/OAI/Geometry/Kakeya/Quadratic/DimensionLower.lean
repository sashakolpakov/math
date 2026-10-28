import OAI.Geometry.Kakeya.Quadratic.CompactExample
import OAI.Geometry.Kakeya.Quadratic.OpenSlopes
import OAI.Geometry.Kakeya.Quadratic.HausdorffProductEuclidean

open Set _root_.MeasureTheory Metric Module
open scoped Topology ENNReal

noncomputable section
namespace OAI.Geometry.Kakeya.Quadratic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The quadratic lifting lower bound.  The only analytic input is the
ordinary linear Kakeya dimension theorem.  The lift, its open family of
linear directions, and its product dimension bound are all explicit. -/
theorem dimH_quadratic_curves_lower (hK : OAI.MeasureTheory.Kakeya.KakeyaConjecture)
    (hn : 1 ≤ finrank ℝ E) (B : E →ₗ[ℝ] E) {τ : ℝ} (hτ : 0 < τ)
    {Y : Set E} (hY : (0 : E) ∈ interior Y) {K : Set (E × ℝ)}
    (hcurves : ∀ y ∈ Y, ∃ w : E, ∀ t ∈ Icc (-τ) τ, curve B y w t ∈ K) :
    (finrank ℝ E - (finrank ℝ B.range - finrank ℝ (B.comp B).range) + 1 : ℕ) ≤
      dimH K := by
  let F := (slope B).range
  let S : E × B.range →ₗ[ℝ] F := (slope B).rangeRestrict
  obtain ⟨R, hR⟩ := S.exists_rightInverse_of_surjective (slope B).range_rangeRestrict
  let P : E × B.range →ₗ[ℝ] F := (slope B).range.subtype.leftInverse
  have hP (v : E × B.range) : P (slope B v) = S v :=
    (slope B).range.subtype.leftInverse_apply_of_inj (slope B).range.ker_subtype (S v)
  have hRa (a : F) : S (R a) = a := LinearMap.congr_fun hR a
  have ho : IsOpen ((fun a : F => (R a).1) ⁻¹' interior Y) :=
    isOpen_interior.preimage (continuous_fst.comp R.continuous_of_finiteDimensional)
  have hzero : (0 : F) ∈ (fun a : F => (R a).1) ⁻¹' interior Y := by simpa using hY
  obtain ⟨ε, hε, hεY⟩ := Metric.isOpen_iff.mp ho 0 hzero
  let L : Set ((E × B.range) × ℝ) := (liftShear B).symm '' (K ×ˢ (univ : Set B.range))
  let proj : ((E × B.range) × ℝ) →ₗ[ℝ] F × ℝ := P.prodMap LinearMap.id
  have hsegments : ∀ a ∈ ball (0 : F) ε, ∃ x : F × ℝ,
      ∀ t ∈ Icc (-τ) τ, x + t • (a, (1 : ℝ)) ∈ proj '' L := by
    intro a ha
    have hya : (R a).1 ∈ Y := interior_subset (hεY ha)
    obtain ⟨w, hw⟩ := hcurves (R a).1 hya
    refine ⟨(P (w, (R a).2), 0), ?_⟩
    intro t ht
    refine ⟨liftedLine B (R a).1 w (R a).2 t, ?_, ?_⟩
    · refine ⟨liftShear B (liftedLine B (R a).1 w (R a).2 t), ?_, ?_⟩
      · refine ⟨?_, mem_univ _⟩
        change liftProjection B (liftedLine B (R a).1 w (R a).2 t) ∈ K
        rw [liftProjection_liftedLine]
        exact hw t ht
      · exact (liftShear B).symm_apply_apply _
    · apply Prod.ext
      · change P ((w, (R a).2) + t • slope B ((R a).1, (R a).2)) = P (w, (R a).2) + t • a
        rw [map_add, map_smul, hP, Prod.eta, hRa]
      · simp [proj, liftedLine]
  have hnF : 1 ≤ finrank ℝ F := by
    change 1 ≤ finrank ℝ (slope B).range
    rw [finrank_slope_range]
    omega
  have hfull : dimH (proj '' L) = (finrank ℝ F + 1 : ℕ) :=
    dimH_eq_of_open_slopes hK hnF hε hτ hsegments
  have hprod : dimH L ≤ dimH K + finrank ℝ B.range := by
    apply le_trans ((contDiff_liftShear_symm B).differentiable (by norm_num)).differentiableOn.dimH_image_le
    exact dimH_prod_univ_le K
  have hproj : dimH (proj '' L) ≤ dimH L :=
    proj.toContinuousLinearMap.differentiable.differentiableOn.dimH_image_le
  have hdim : (finrank ℝ E + finrank ℝ (B.comp B).range + 1 : ℕ) ≤
      dimH K + finrank ℝ B.range := by
    have H := hproj.trans hprod
    rw [hfull] at H
    simpa only [F, finrank_slope_range] using H
  have hrank : finrank ℝ B.range ≤ finrank ℝ E := B.finrank_range_le
  have hrank2 : finrank ℝ (B.comp B).range ≤ finrank ℝ B.range := by
    rw [← range_restricted]
    exact (B.comp B.range.subtype).finrank_range_le
  have harith : (finrank ℝ E - (finrank ℝ B.range - finrank ℝ (B.comp B).range) + 1) +
      finrank ℝ B.range = finrank ℝ E + finrank ℝ (B.comp B).range + 1 := by omega
  apply (ENNReal.add_le_add_iff_right (by simp : (finrank ℝ B.range : ℝ≥0∞) ≠ ⊤)).mp
  simpa only [← Nat.cast_add, harith] using hdim

end OAI.Geometry.Kakeya.Quadratic
