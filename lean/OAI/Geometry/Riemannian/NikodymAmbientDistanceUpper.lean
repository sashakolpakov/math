import OAI.Geometry.Riemannian.NikodymAmbientDistanceLower

noncomputable section
open Set Bundle Manifold _root_.MeasureTheory Filter Metric
open scoped ContDiff ENNReal NNReal Topology

namespace OAI.Geometry.Riemannian

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

def inverseModelMFDeriv (f : E → M) (x : E) : E →L[ℝ] TangentSpace 𝓘(ℝ,E) (f x) :=
  mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) f x

/-- Two-point upper bound for ambient distance by coordinate distance, obtained by
pushing the segment between the coordinates through the inverse chart. -/
theorem exists_ambient_chart_upper (a : M) :
    ∃ C : ℝ≥0, 0 < C ∧ ∃ U : Set M, IsOpen U ∧ a ∈ U ∧
      U ⊆ (extChartAt 𝓘(ℝ,E) a).source ∧
      ∀ y ∈ U, ∀ z ∈ U,
        edist y z ≤ (C : ℝ≥0∞) *
          edist (extChartAt 𝓘(ℝ,E) a y) (extChartAt 𝓘(ℝ,E) a z) := by
  let e := extChartAt 𝓘(ℝ,E) a
  have hrange : Set.range (𝓘(ℝ,E) : E → E) = univ := Set.range_id
  obtain ⟨C, hC, hder⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt 𝓘(ℝ,E) a
  simp only [hrange, nhdsWithin_univ, mfderivWithin_univ] at hder
  have hder' : ∀ᶠ w in 𝓝 (e a), ‖inverseModelMFDeriv e.symm w‖ₑ < C := by
    exact hder
  have htarget : e.target ∈ 𝓝 (e a) := extChartAt_target_mem_nhds a
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem htarget hder')
  let U : Set M := e.source ∩ e ⁻¹' Metric.ball (e a) r
  refine ⟨C, hC, U, isOpen_extChartAt_preimage' a isOpen_ball, ?_, inter_subset_left, ?_⟩
  · exact ⟨mem_extChartAt_source a, mem_ball_self hr⟩
  · intro y hy z hz
    let η := ContinuousAffineMap.lineMap (R := ℝ) (e y) (e z)
    let γ : ℝ → M := e.symm ∘ η
    have hη : MapsTo η (Icc 0 1) (e.target ∩
        {w | ‖inverseModelMFDeriv e.symm w‖ₑ < C}) := by
      intro t ht
      apply hball
      exact (convex_ball (e a) r).lineMap_mem hy.2 hz.2 ht
    have hηsmooth : ContMDiff 𝓘(ℝ) 𝓘(ℝ,E) 1 η := by
      rw [contMDiff_iff_contDiff]
      exact ContinuousAffineMap.contDiff _
    have hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ,E) 1 γ (Icc 0 1) :=
      (contMDiffOn_extChartAt_symm a).comp hηsmooth.contMDiffOn (fun t ht => (hη ht).1)
    have hγ0 : γ 0 = y := by
      simp only [γ, Function.comp_apply, η, ContinuousAffineMap.coe_lineMap_eq,
        AffineMap.lineMap_apply_zero]
      exact e.left_inv hy.1
    have hγ1 : γ 1 = z := by
      simp only [γ, Function.comp_apply, η, ContinuousAffineMap.coe_lineMap_eq,
        AffineMap.lineMap_apply_one]
      exact e.left_inv hz.1
    have hdist : edist y z ≤ pathELength 𝓘(ℝ,E) γ 0 1 := by
      rw [IsRiemannianManifold.out (I := 𝓘(ℝ,E))]
      exact riemannianEDist_le_pathELength hγ hγ0 hγ1 zero_le_one
    apply hdist.trans
    rw [← lintegral_fderiv_lineMap_eq_edist,
      pathELength_eq_lintegral_mfderivWithin_Icc,
      ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    have hchain : mfderivWithin 𝓘(ℝ) 𝓘(ℝ,E) γ (Icc 0 1) t =
        (mfderivWithin 𝓘(ℝ,E) 𝓘(ℝ,E) e.symm (Set.range 𝓘(ℝ,E)) (η t)).comp
          (mfderivWithin 𝓘(ℝ) 𝓘(ℝ,E) η (Icc 0 1) t) := by
      apply mfderivWithin_comp
      · exact mdifferentiableWithinAt_extChartAt_symm (hη ht).1
      · exact (hηsmooth.mdifferentiable one_ne_zero).mdifferentiableOn _ ht
      · intro s hs
        exact extChartAt_target_subset_range a (hη hs).1
      · exact (uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt
    have happly := congrArg (fun A => A 1) hchain
    simp only [hrange, mfderivWithin_univ] at happly
    rw [happly]
    change ‖inverseModelMFDeriv e.symm (η t)
      (mfderivWithin 𝓘(ℝ) 𝓘(ℝ,E) η (Icc 0 1) t 1)‖ₑ ≤ _
    apply (ContinuousLinearMap.le_opENorm _ _).trans
    gcongr
    · exact (hη ht).2.le
    · simp only [mfderivWithin_eq_fderivWithin]
      exact le_rfl

end OAI.Geometry.Riemannian
