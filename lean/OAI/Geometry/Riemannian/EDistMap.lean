import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! Bounded differentials decrease Riemannian path distance by the same factor. -/

noncomputable section

open Bundle Set _root_.MeasureTheory Manifold
open scoped NNReal ENNReal ContDiff Topology

namespace OAI.Geometry.Riemannian

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

attribute [local instance] Measure.Subtype.measureSpace

/-- The image of a `C¹` path has length at most the differential bound times its length. -/
theorem mapped_path_length_le {f : M → N} (hf : ContMDiff I J 1 f)
    {C : ℝ≥0} (hbound : ∀ x, ‖mfderiv I J f x‖ₑ ≤ C)
    {x y : M} (γ : Path x y) (hγ : CMDiff 1 γ) :
    (∫⁻ t, ‖mfderiv% (γ.map hf.continuous) t 1‖ₑ) ≤
      (C : ℝ≥0∞) * ∫⁻ t, ‖mfderiv% γ t 1‖ₑ := by
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply lintegral_mono
  intro t
  change ‖mfderiv _ J (f ∘ γ) t 1‖ₑ ≤ _
  rw [mfderiv_comp_apply t ((hf.mdifferentiable one_ne_zero) (γ t))
    ((hγ.mdifferentiable one_ne_zero) t)]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  dsimp only
  gcongr
  exact hbound (γ t)

/-- Real operator-norm form of the path-length estimate. -/
theorem mapped_path_length_le_norm {f : M → N} (hf : ContMDiff I J 1 f)
    {C : ℝ≥0} (hbound : ∀ x, ‖mfderiv I J f x‖ ≤ C)
    {x y : M} (γ : Path x y) (hγ : CMDiff 1 γ) :
    (∫⁻ t, ‖mfderiv% (γ.map hf.continuous) t 1‖ₑ) ≤
      (C : ℝ≥0∞) * ∫⁻ t, ‖mfderiv% γ t 1‖ₑ := by
  apply mapped_path_length_le hf (γ := γ) (hγ := hγ)
  intro x
  exact_mod_cast hbound x

/-- A positive finite differential bound controls the actual Riemannian extended distance.
Positivity is necessary if the source has distinct path components. -/
theorem riemannianEDist_map_le {f : M → N} (hf : ContMDiff I J 1 f)
    {C : ℝ≥0} (hC : 0 < C) (hbound : ∀ x, ‖mfderiv I J f x‖ₑ ≤ C)
    (x y : M) :
    riemannianEDist J (f x) (f y) ≤ (C : ℝ≥0∞) * riemannianEDist I x y := by
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hC.ne'
  conv_rhs => rw [riemannianEDist]
  rw [ENNReal.mul_iInf_of_ne hC0 ENNReal.coe_ne_top]
  apply le_iInf
  intro γ
  rw [ENNReal.mul_iInf_of_ne hC0 ENNReal.coe_ne_top]
  apply le_iInf
  intro hγ
  have himg : CMDiff 1 (γ.map hf.continuous) := by
    exact hf.comp hγ
  have hle : riemannianEDist J (f x) (f y) ≤
      ∫⁻ t, ‖mfderiv% (γ.map hf.continuous) t 1‖ₑ := by
    rw [riemannianEDist]
    exact biInf_le _ himg
  exact hle.trans (mapped_path_length_le hf hbound γ hγ)

/-- Real operator-norm form of the global distance estimate. -/
theorem riemannianEDist_map_le_norm {f : M → N} (hf : ContMDiff I J 1 f)
    {C : ℝ≥0} (hC : 0 < C) (hbound : ∀ x, ‖mfderiv I J f x‖ ≤ C)
    (x y : M) :
    riemannianEDist J (f x) (f y) ≤ (C : ℝ≥0∞) * riemannianEDist I x y := by
  apply riemannianEDist_map_le hf hC (x := x) (y := y)
  intro z
  exact_mod_cast hbound z

/-- If the target's given metric is Riemannian, the same bound holds for its `edist`. -/
theorem edist_map_le_riemannianEDist
    [PseudoEMetricSpace N] [IsRiemannianManifold J N]
    {f : M → N} (hf : ContMDiff I J 1 f)
    {C : ℝ≥0} (hC : 0 < C) (hbound : ∀ x, ‖mfderiv I J f x‖ ≤ C)
    (x y : M) :
    edist (f x) (f y) ≤ (C : ℝ≥0∞) * riemannianEDist I x y := by
  rw [IsRiemannianManifold.out (I := J)]
  exact riemannianEDist_map_le_norm hf hC hbound x y

/-- A globally bounded differential gives a Lipschitz map between Riemannian manifolds. -/
theorem lipschitzWith_of_mfderiv_bound
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [PseudoEMetricSpace N] [IsRiemannianManifold J N]
    {f : M → N} (hf : ContMDiff I J 1 f)
    {C : ℝ≥0} (hC : 0 < C) (hbound : ∀ x, ‖mfderiv I J f x‖ ≤ C) :
    LipschitzWith C f := by
  intro x y
  conv_rhs => rw [IsRiemannianManifold.out (I := I)]
  exact edist_map_le_riemannianEDist hf hC hbound x y

end OAI.Geometry.Riemannian
