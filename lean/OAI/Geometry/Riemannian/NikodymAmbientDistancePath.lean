import OAI.Geometry.Riemannian.EDistMap

noncomputable section
open Set Bundle Manifold _root_.MeasureTheory Filter Metric
open scoped ContDiff ENNReal NNReal Topology

namespace OAI.Geometry.Riemannian

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance (x : F) : NormedAddCommGroup (TangentSpace 𝓘(ℝ,F) x) :=
  normedAddCommGroupTangentSpaceVectorSpace x
local instance (x : F) : NormedSpace ℝ (TangentSpace 𝓘(ℝ,F) x) :=
  normedSpaceTangentSpaceVectorSpace x

/-- The differential of a vector-valued map, with the codomain written as the actual
model space. This avoids imposing a second norm on that model's tangent alias. -/
def modelMFDeriv (f : M → F) (x : M) : TangentSpace I x →L[ℝ] F :=
  mfderiv I 𝓘(ℝ,F) f x

omit [IsManifold I 1 M] [IsRiemannianManifold I M] in
/-- A chart-valued map with bounded differential controls endpoints of any path staying
in its domain. This is a statement about the actual integral of the path speed. -/
theorem image_edist_le_path_length {s : Set M} (hs : IsOpen s)
    {f : M → F} (hf : ContMDiffOn I 𝓘(ℝ,F) 1 f s)
    {C : ℝ≥0} (hC : ∀ x ∈ s, ‖modelMFDeriv (I := I) f x‖ₑ ≤ C)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ)
    (hmap : MapsTo γ (Icc 0 1) s) :
    edist (f (γ 0)) (f (γ 1)) ≤ (C : ℝ≥0∞) * pathELength I γ 0 1 := by
  let η : ℝ → F := f ∘ γ
  have hη : ContDiffOn ℝ 1 η (Icc 0 1) := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact hf.comp hγ.contMDiffOn hmap
  have hFTC := enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hη zero_le_one
  have hfirst : edist (f (γ 0)) (f (γ 1)) ≤
      ∫⁻ t in Icc 0 1, ‖mfderivWithin 𝓘(ℝ) 𝓘(ℝ,F) η (Icc 0 1) t 1‖ₑ := by
    rw [edist_comm, edist_eq_enorm_sub]
    simpa only [mfderivWithin_eq_fderivWithin, ← fderivWithin_derivWithin] using! hFTC
  apply hfirst.trans
  rw [pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc
  intro t ht
  have hchain := mfderiv_comp_mfderivWithin t
    (((hf (γ t) (hmap ht)).contMDiffAt (hs.mem_nhds (hmap ht))).mdifferentiableAt one_ne_zero)
    ((hγ.mdifferentiable one_ne_zero).mdifferentiableOn _ ht)
    ((uniqueDiffOn_Icc zero_lt_one t ht).uniqueMDiffWithinAt)
  have heq : mfderivWithin 𝓘(ℝ) 𝓘(ℝ,F) η (Icc 0 1) t 1 =
      mfderiv I 𝓘(ℝ,F) f (γ t) (mfderivWithin 𝓘(ℝ) I γ (Icc 0 1) t 1) := by
    exact congrArg (fun A => A 1) hchain
  rw [heq]
  change ‖modelMFDeriv (I := I) f (γ t)
    (mfderivWithin 𝓘(ℝ) I γ (Icc 0 1) t 1)‖ₑ ≤ _
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  exact hC _ (hmap ht)

omit [IsManifold I 1 M] in
/-- A path of length less than `R` starting in the `R`-ball stays in the `2R`-ball.
The distance here is the ambient Riemannian distance, not a restricted-domain distance. -/
theorem short_path_stays_in_eball {a y : M} {R : ℝ≥0}
    (hy : y ∈ Metric.eball a (R : ℝ≥0∞))
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ) (hγ0 : γ 0 = y)
    (hlen : pathELength I γ 0 1 < R) :
    MapsTo γ (Icc 0 1) (Metric.eball a (2 * (R : ℝ≥0∞))) := by
  intro t ht
  have hprefix : edist y (γ t) ≤ pathELength I γ 0 t := by
    rw [IsRiemannianManifold.out (I := I)]
    exact riemannianEDist_le_pathELength hγ.contMDiffOn hγ0 rfl ht.1
  have hpartial : pathELength I γ 0 t ≤ pathELength I γ 0 1 :=
    pathELength_mono le_rfl ht.2
  have hdist : edist (γ t) y < R := by
    rw [edist_comm]
    exact hprefix.trans_lt (hpartial.trans_lt hlen)
  exact (edist_triangle (γ t) y a).trans_lt (by
    have := ENNReal.add_lt_add hdist hy
    simpa only [two_mul] using this)

omit [IsManifold I 1 M] [NormedSpace ℝ F] in
/-- A bound for all genuine smooth path lengths descends to the ambient distance. -/
theorem image_edist_le_of_path_bound {f : M → F} {y z : M}
    {K : ℝ≥0} (hK : 0 < K)
    (hb : ∀ γ : ℝ → M, ContMDiff 𝓘(ℝ) I 1 γ → γ 0 = y → γ 1 = z →
      edist (f y) (f z) ≤ (K : ℝ≥0∞) * pathELength I γ 0 1) :
    edist (f y) (f z) ≤ (K : ℝ≥0∞) * edist y z := by
  have hK0 : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hK.ne'
  by_contra hn
  have hlt : (K : ℝ≥0∞) * edist y z < edist (f y) (f z) := lt_of_not_ge hn
  have hd : riemannianEDist I y z < edist (f y) (f z) / K := by
    rw [← IsRiemannianManifold.out (I := I)]
    apply (ENNReal.lt_div_iff_mul_lt (Or.inl hK0) (Or.inl ENNReal.coe_ne_top)).mpr
    simpa only [mul_comm] using hlt
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hd zero_lt_one
  have hs : (K : ℝ≥0∞) * pathELength I γ 0 1 < edist (f y) (f z) := by
    have hh := (ENNReal.lt_div_iff_mul_lt (Or.inl hK0)
      (Or.inl ENNReal.coe_ne_top)).mp hlen
    simpa only [mul_comm] using hh
  exact (not_lt_of_ge (hb γ hγ hγ0 hγ1)) hs

omit [IsManifold I 1 M] in
/-- Two-point local comparison with ambient distance: short paths remain in the chart,
while a diameter bound controls long paths. -/
theorem image_edist_le_on_eball {a y z : M} {R C K : ℝ≥0} {f : M → F}
    (hK : 0 < K) (hCK : C ≤ K)
    (hf : ContMDiffOn I 𝓘(ℝ,F) 1 f (Metric.eball a (2 * (R : ℝ≥0∞))))
    (hC : ∀ x ∈ Metric.eball a (2 * (R : ℝ≥0∞)),
      ‖modelMFDeriv (I := I) f x‖ₑ ≤ C)
    (hy : y ∈ Metric.eball a (R : ℝ≥0∞))
    (hdiam : edist (f y) (f z) ≤ (K : ℝ≥0∞) * R) :
    edist (f y) (f z) ≤ (K : ℝ≥0∞) * edist y z := by
  apply image_edist_le_of_path_bound (I := I) hK
  intro γ hγ hγ0 hγ1
  by_cases hs : pathELength I γ 0 1 < R
  · have hm := short_path_stays_in_eball hy hγ hγ0 hs
    have hb := image_edist_le_path_length isOpen_eball hf hC hγ hm
    rw [hγ0, hγ1] at hb
    apply hb.trans
    gcongr
  · apply hdiam.trans
    gcongr
    exact le_of_not_gt hs

end OAI.Geometry.Riemannian
