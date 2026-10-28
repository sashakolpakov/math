import OAI.AlgebraicTopology.FundamentalClass.AffineOrientation
import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import OAI.AlgebraicTopology.DeRham.Comparison.CubeNeighborhoodExtension

/-! # Chart Integral -/

namespace OAI.AlgebraicTopology.FundamentalClass.ChartIntegral.IntegrationConstruction

noncomputable section

section

/-! Compute simplex integration inside a manifold chart. The chart map on
the simplex is a positive affine map, so the Jacobian has positive sign. -/

open _root_.CategoryTheory Set Filter _root_.MeasureTheory
open OAI.AlgebraicTopology.DeRham.Comparison.CubeNeighborhoodExtension
open scoped _root_.Manifold ContDiff _root_.Topology Simplicial

set_option backward.isDefEq.respectTransparency false

theorem positiveAffine_contDiff (d : ℕ) (a : Fin d → ℝ) (r : ℝ) :
    ContDiff ℝ ∞ (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r) := by
  change ContDiff ℝ ∞ (fun x : Fin d → ℝ => a + r • x)
  exact contDiff_const.add (contDiff_id.const_smul r)

theorem positiveAffine_hasFDerivAt (d : ℕ) (a : Fin d → ℝ) (r : ℝ) (x : Fin d → ℝ) :
    HasFDerivAt (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r)
      (r • ContinuousLinearMap.id ℝ (Fin d → ℝ)) x :=
  ((hasFDerivAt_id x).const_smul r).const_add a

theorem positiveAffine_det (d : ℕ) (a : Fin d → ℝ) (r : ℝ) (x : Fin d → ℝ) :
    (fderiv ℝ (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r) x).toLinearMap.det = r ^ d := by
  rw [(positiveAffine_hasFDerivAt d a r x).fderiv]
  change (r • (LinearMap.id : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ))).det = _
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one]
  simp

variable {d : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
    [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]

theorem pullback_top_in_affine_chart (g : (Fin d → ℝ) → M)
    (hg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ∞ g)
    (e : OpenPartialHomeomorph M (Fin d → ℝ)) (he : e ∈ atlas (Fin d → ℝ) M)
    (a : Fin d → ℝ) (r : ℝ)
    (hsource : MapsTo g (SimplexGeometry.IntegrationConstruction.positiveInterior d) e.source)
    (hcoords : EqOn (e ∘ g) (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r) (SimplexGeometry.IntegrationConstruction.positiveInterior d))
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d)
    (x : Fin d → ℝ) (hx : x ∈ SimplexGeometry.IntegrationConstruction.positiveInterior d) :
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback g hg form).toNormedSpace x (Pi.basisFun ℝ (Fin d)) =
      r ^ d • form.val.inChart e (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r x) (Pi.basisFun ℝ (Fin d)) := by
  have h := form.val.pullback_inChart g (OpenPartialHomeomorph.refl (Fin d → ℝ)) e
    (by simp) he (y := x) (by simp) (hsource hx) ((hg.mdifferentiable (by simp)) x)
  simp only [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_refl, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply, Function.comp_id, id_eq] at h
  have hevent : (e ∘ g) =ᶠ[𝓝 x] AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r := by
    filter_upwards [(SimplexGeometry.IntegrationConstruction.positiveInterior_isOpen d).mem_nhds hx] with y hy
    exact hcoords hy
  have hd : fderiv ℝ (e ∘ g) x = fderiv ℝ (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r) x :=
    hevent.fderiv_eq
  have heq : e (g x) = AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r x := hcoords hx
  change (form.val.pullback g).toNormedSpace x _ = _
  rw [h, heq, hd]
  change form.val.inChart e (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r x)
    (fun i => fderiv ℝ (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r) x (Pi.basisFun ℝ (Fin d) i)) = _
  have ht := DeRham.Comparison.TopBidegree.topAlternating_comp_apply (Pi.basisFun ℝ (Fin d))
    (form.val.inChart e (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r x)).toAlternatingMap
    (fderiv ℝ (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r) x).toLinearMap (Pi.basisFun ℝ (Fin d))
  rw [positiveAffine_det] at ht
  simpa only [ContinuousAlternatingMap.coe_toAlternatingMap, Function.comp_def,
    ContinuousLinearMap.coe_coe] using ht

theorem smoothSimplexIntegration_affine_chart (g : (Fin d → ℝ) → M)
    (hg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ∞ g)
    (e : OpenPartialHomeomorph M (Fin d → ℝ)) (he : e ∈ atlas (Fin d → ℝ) M)
    (a : Fin d → ℝ) (r : ℝ) (hr : 0 < r)
    (hsource : MapsTo g (SimplexGeometry.IntegrationConstruction.positiveInterior d) e.source)
    (hcoords : EqOn (e ∘ g) (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r) (SimplexGeometry.IntegrationConstruction.positiveInterior d))
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (Fin d → ℝ) M d) :
    DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration
      ((Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothSingularMap (Fin d → ℝ) (Fin d → ℝ) g hg).app _ (SimplexGeometry.IntegrationConstruction.positiveSmoothSimplex d)) form =
      ∫ y in AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r '' SimplexGeometry.IntegrationConstruction.positiveInterior d,
        form.val.inChart e y (Pi.basisFun ℝ (Fin d)) := by
  rw [DeRham.Comparison.SmoothSimplexIntegration.smoothSimplexIntegration_postcompose, SimplexGeometry.IntegrationConstruction.positiveSmoothSimplex_integral_interior]
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume
    (SimplexGeometry.IntegrationConstruction.positiveInterior_isOpen d).measurableSet
    (fun x _ => (positiveAffine_hasFDerivAt d a r x).hasFDerivWithinAt)
    (AffineOrientation.IntegrationConstruction.positiveAffine_injective (Fin d → ℝ) a r hr).injOn
    (fun y => form.val.inChart e y (Pi.basisFun ℝ (Fin d)))
  rw [h]
  apply setIntegral_congr_fun (SimplexGeometry.IntegrationConstruction.positiveInterior_isOpen d).measurableSet
  intro x hx
  dsimp only
  rw [pullback_top_in_affine_chart g hg e he a r hsource hcoords form x hx]
  have hd : (r • ContinuousLinearMap.id ℝ (Fin d → ℝ)).det = r ^ d := by
    rw [← (positiveAffine_hasFDerivAt d a r x).fderiv]
    exact positiveAffine_det d a r x
  rw [hd, abs_of_pos (pow_pos hr d)]

end

/-! Small chart simplices have genuine globally smooth parameter maps.
The maps agree with the inverse affine chart on the entire closed simplex. -/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex
open _root_.CategoryTheory Set Filter _root_.TopologicalSpace
open OAI.AlgebraicTopology.DeRham.Comparison.CubeNeighborhoodExtension
open scoped _root_.Manifold ContDiff _root_.Topology Simplicial

set_option backward.isDefEq.respectTransparency false

theorem positiveSimplex_shift_mem_cube (d : ℕ)
    (t : Convexity.StdSimplex ℝ (Fin (d + 1))) :
    LocalSimplex.IntegrationGeometry.positiveSimplex d t + SimplexGeometry.IntegrationConstruction.simplexBarycenter d ∈ DeRham.Comparison.StokesF.SingularCubeStokes.unitCube d := by
  constructor
  · intro i
    change 0 ≤ t.weights i.succ - ((d + 1 : ℕ) : ℝ)⁻¹ + ((d + 1 : ℕ) : ℝ)⁻¹
    rw [sub_add_cancel]
    exact t.weights_nonneg i.succ
  · intro i
    change t.weights i.succ - ((d + 1 : ℕ) : ℝ)⁻¹ + ((d + 1 : ℕ) : ℝ)⁻¹ ≤ 1
    rw [sub_add_cancel]
    exact t.weights_apply_le_one i.succ

theorem positiveInterior_shift_mem_cube (d : ℕ) (x : Fin d → ℝ) (hx : x ∈ SimplexGeometry.IntegrationConstruction.positiveInterior d) :
    x + SimplexGeometry.IntegrationConstruction.simplexBarycenter d ∈ DeRham.Comparison.StokesF.SingularCubeStokes.unitCube d := by
  change x + SimplexGeometry.IntegrationConstruction.simplexBarycenter d ∈ DuffyDomain.IntegrationConstruction.Duffy.simplexInterior d at hx
  constructor
  · intro i
    exact (hx.1 i).le
  · intro i
    exact (Finset.single_le_sum (fun j _ => (hx.1 j).le) (Finset.mem_univ i)).trans hx.2.le

theorem unitCube_norm_le_one (d : ℕ) (t : Fin d → ℝ) (ht : t ∈ DeRham.Comparison.StokesF.SingularCubeStokes.unitCube d) :
    ‖t‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  rw [Real.norm_of_nonneg (ht.1 i)]
  exact ht.2 i

theorem exists_small_affine_cube (d : ℕ) (U : Set (Fin d → ℝ)) (hU : IsOpen U)
    (a : Fin d → ℝ) (ha : a ∈ U) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ DeRham.Comparison.StokesF.SingularCubeStokes.unitCube d,
      AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r (t - SimplexGeometry.IntegrationConstruction.simplexBarycenter d) ∈ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU a ha
  let B : ℝ := 1 + ‖SimplexGeometry.IntegrationConstruction.simplexBarycenter d‖
  have hB : 0 < B := by dsimp [B]; positivity
  let r := ε / (2 * B)
  have hr : 0 < r := div_pos hε (mul_pos (by norm_num) hB)
  refine ⟨r, hr, ?_⟩
  intro t ht
  apply hball
  rw [Metric.mem_ball, dist_eq_norm]
  change ‖a + r • (t - SimplexGeometry.IntegrationConstruction.simplexBarycenter d) - a‖ < ε
  rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
  have hb : ‖t - SimplexGeometry.IntegrationConstruction.simplexBarycenter d‖ ≤ B := by
    have ht' := unitCube_norm_le_one d t ht
    have htri := norm_sub_le t (SimplexGeometry.IntegrationConstruction.simplexBarycenter d)
    dsimp only [B]
    linarith
  have heq : r * B = ε / 2 := by dsimp [r]; field_simp
  calc
    r * ‖t - SimplexGeometry.IntegrationConstruction.simplexBarycenter d‖ ≤ r * B := mul_le_mul_of_nonneg_left hb hr.le
    _ = ε / 2 := heq
    _ < ε := by linarith

variable {d : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
    [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]

theorem exists_smooth_chart_simplex_parameter
    (e : OpenPartialHomeomorph M (Fin d → ℝ)) (he : e ∈ atlas (Fin d → ℝ) M)
    (a : Fin d → ℝ) (r : ℝ)
    (hcube : ∀ t ∈ DeRham.Comparison.StokesF.SingularCubeStokes.unitCube d,
      AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r (t - SimplexGeometry.IntegrationConstruction.simplexBarycenter d) ∈ e.target) :
    ∃ g : (Fin d → ℝ) → M,
      ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ∞ g ∧
      ∀ x, x + SimplexGeometry.IntegrationConstruction.simplexBarycenter d ∈ DeRham.Comparison.StokesF.SingularCubeStokes.unitCube d →
        g x = e.symm (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r x) ∧ g x ∈ e.source := by
  let parameter : (Fin d → ℝ) → (Fin d → ℝ) :=
    fun t => AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r (t - SimplexGeometry.IntegrationConstruction.simplexBarycenter d)
  have hp : ContDiff ℝ ∞ parameter :=
    (positiveAffine_contDiff d a r).comp (contDiff_id.sub contDiff_const)
  let U : Opens (Fin d → ℝ) := ⟨parameter ⁻¹' e.target, e.open_target.preimage hp.continuous⟩
  let f : U → M := fun t => e.symm (parameter t.val)
  have hf : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ∞ f :=
    (contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he)).comp_contMDiff
      (hp.contMDiff.comp contMDiff_subtype_val) (fun t => t.property)
  obtain ⟨G, hG, hagree⟩ := DeRham.Comparison.CubeNeighborhoodExtension.exists_global_contMDiff_of_cube_neighborhood
    (𝓘(ℝ, Fin d → ℝ)) U (fun t ht => hcube t ht) hf
  refine ⟨fun x => G (x + SimplexGeometry.IntegrationConstruction.simplexBarycenter d),
    hG.comp (contDiff_id.add contDiff_const).contMDiff, ?_⟩
  intro x hx
  obtain ⟨hxu, heq⟩ := hagree.self_of_nhdsSet (x + SimplexGeometry.IntegrationConstruction.simplexBarycenter d) hx
  have hpval : parameter (x + SimplexGeometry.IntegrationConstruction.simplexBarycenter d) = AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r x := by
    dsimp only [parameter]
    rw [add_sub_cancel_right]
  have hval : G (x + SimplexGeometry.IntegrationConstruction.simplexBarycenter d) = e.symm (AffineOrientation.IntegrationConstruction.positiveAffine (Fin d → ℝ) a r x) := by
    simpa only [f, hpval] using heq
  refine ⟨hval, ?_⟩
  change G (x + SimplexGeometry.IntegrationConstruction.simplexBarycenter d) ∈ e.source
  rw [hval]
  change parameter (x + SimplexGeometry.IntegrationConstruction.simplexBarycenter d) ∈ e.target at hxu
  exact e.map_target (hpval ▸ hxu)

end

end OAI.AlgebraicTopology.FundamentalClass.ChartIntegral.IntegrationConstruction
