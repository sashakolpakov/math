import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialLocal
import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-! # Exponential Smooth -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialSmooth.Constructions.Exponential

noncomputable section

/-!
# DegreeTwo: smoothness of the constructed exponential

The invariant vector field is smooth because it is obtained by differentiating
group multiplication. The integral-curve equation then improves the curve's
regularity one derivative at a time. The finite-coordinate exponential formula
transfers that smoothness to the exponential itself.
-/

open _root_.Manifold
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup (𝓘(ℝ, E)) ∞ G]

local instance : LieGroup (𝓘(ℝ, E)) (minSmoothness ℝ 3) G := by
  rw [minSmoothness_of_isRCLikeNormedField]
  infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual invariant field is smooth to every order. -/
theorem invariant_contMDiff (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞
      (fun g => (mulInvariantVectorField v g : TangentBundle (𝓘(ℝ, E)) G)) := by
  let I := 𝓘(ℝ, E)
  let fg : G → TangentBundle I G := fun g => Bundle.TotalSpace.mk' E g 0
  have sfg : ContMDiff I I.tangent ∞ fg := Bundle.contMDiff_zeroSection _ _
  let fv : G → TangentBundle I G := fun _ => Bundle.TotalSpace.mk' E 1 v
  have sfv : ContMDiff I I.tangent ∞ fv := contMDiff_const
  let F₁ : G → TangentBundle I G × TangentBundle I G := fun g => (fg g, fv g)
  have S₁ : ContMDiff I (I.tangent.prod I.tangent) ∞ F₁ := sfg.prodMk sfv
  let F₂ : TangentBundle I G × TangentBundle I G → TangentBundle (I.prod I) (G × G) :=
    (equivTangentBundleProd I G I G).symm
  have S₂ : ContMDiff (I.tangent.prod I.tangent) (I.prod I).tangent ∞ F₂ :=
    contMDiff_equivTangentBundleProd_symm
  let F₃ : TangentBundle (I.prod I) (G × G) → TangentBundle I G :=
    tangentMap (I.prod I) I (fun p : G × G => p.1 * p.2)
  have S₃ : ContMDiff (I.prod I).tangent I.tangent ∞ F₃ := by
    apply ContMDiff.contMDiff_tangentMap _ (m := ∞) le_rfl
    simpa using contMDiff_mul I (n := ∞) (G := G)
  let S := (S₃.comp S₂).comp S₁
  convert! S with g
  · simp [F₁, F₂, F₃, fg, fv]
  · simp only [Function.comp_apply, tangentMap, F₃, F₂, F₁, fg, fv]
    rw [mfderiv_prod_eq_add_apply ((contMDiff_mul I (n := ∞) (G := G)).mdifferentiableAt
      (by simp))]
    simp +instances [mulInvariantVectorField, I]

variable [CompleteSpace E] [T2Space G]

/-- The integral-curve equation inductively supplies every finite derivative. -/
theorem curve_contMDiff_nat (v : GroupLieAlgebra (𝓘(ℝ, E)) G) (n : ℕ) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) n (ExponentialM.Constructions.Exponential.curve v) := by
  induction n with
  | zero => exact contMDiff_zero_iff.mpr (ExponentialM.Constructions.Exponential.curve_continuous v)
  | succ n ih =>
    intro t₀
    let S : ℝ → TangentBundle (𝓘(ℝ, E)) G :=
      fun t => ⟨ExponentialM.Constructions.Exponential.curve v t, mulInvariantVectorField v (ExponentialM.Constructions.Exponential.curve v t)⟩
    let T := trivializationAt E (TangentSpace (𝓘(ℝ, E))) (ExponentialM.Constructions.Exponential.curve v t₀)
    let U : Set ℝ := S ⁻¹' T.source
    let φ : ℝ → E := fun t => (T (S t)).2
    have hS : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)).tangent n S :=
      ((invariant_contMDiff v).of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).comp ih
    have hU : IsOpen U := T.open_source.preimage hS.continuous
    have ht₀ : t₀ ∈ U := by
      change S t₀ ∈ T.source
      simp [T, S, TangentBundle.trivializationAt_source]
    have hφ : ContDiffAt ℝ n φ t₀ :=
      ((T.contMDiffAt_iff ht₀).mp (hS t₀)).2.contDiffAt
    have hder (t : ℝ) (ht : t ∈ U) :
        HasDerivAt (extChartAt (𝓘(ℝ, E)) (ExponentialM.Constructions.Exponential.curve v t₀) ∘ ExponentialM.Constructions.Exponential.curve v) (φ t) t := by
      have hsrc : ExponentialM.Constructions.Exponential.curve v t ∈ (extChartAt (𝓘(ℝ, E)) (ExponentialM.Constructions.Exponential.curve v t₀)).source := by
        simpa only [U, S, T, Set.mem_preimage, TangentBundle.trivializationAt_source,
          extChartAt_source] using ht
      exact (((ExponentialM.Constructions.Exponential.curve_integral v).isMIntegralCurveOn Set.univ).hasDerivWithinAt
        (t₀ := t₀) (Set.mem_univ t) hsrc).hasDerivAt Filter.univ_mem
    have hchart : ContDiffAt ℝ (n + 1)
        (extChartAt (𝓘(ℝ, E)) (ExponentialM.Constructions.Exponential.curve v t₀) ∘ ExponentialM.Constructions.Exponential.curve v) t₀ := by
      apply contDiffAt_succ_iff_hasFDerivAt.mpr
      refine ⟨fun t => (1 : ℝ →L[ℝ] ℝ).smulRight (φ t),
        ⟨U, hU.mem_nhds ht₀, fun t ht => (hder t ht).hasFDerivAt⟩, ?_⟩
      exact (ContinuousLinearMap.smulRightL ℝ ℝ E (1 : ℝ →L[ℝ] ℝ)).contDiff.contDiffAt.comp t₀ hφ
    exact contMDiffAt_iff_target.mpr ⟨(ExponentialM.Constructions.Exponential.curve_continuous v).continuousAt, hchart.contMDiffAt⟩

theorem curve_contMDiff (v : GroupLieAlgebra (𝓘(ℝ, E)) G) :
    ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) ∞ (ExponentialM.Constructions.Exponential.curve v) :=
  contMDiff_infty.mpr (curve_contMDiff_nat v)

variable {C : Type*} [TopologicalSpace C] [ChartedSpace E C] [CommGroup C]
  [LieGroup (𝓘(ℝ, E)) ∞ C] [T2Space C]

/-- The constructed exponential is smooth in all tangent directions. -/
theorem expMap_contMDiff [FiniteDimensional ℝ E] :
    ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (ExponentialM.Constructions.Exponential.expMap (E := E) (C := C)) := by
  let b := Module.finBasis ℝ E
  have he : ExponentialM.Constructions.Exponential.expMap (E := E) (C := C) = fun x =>
      ∏ i, ExponentialM.Constructions.Exponential.curve (G := C) (show GroupLieAlgebra (𝓘(ℝ, E)) C from b i) (b.repr x i) :=
    funext (ExponentialM.Constructions.Exponential.expMap_basis b)
  rw [he]
  apply ContMDiff.prod
  intro i _
  exact (curve_contMDiff (G := C) (show GroupLieAlgebra (𝓘(ℝ, E)) C from b i)).comp
    (b.coord i).toContinuousLinearMap.contDiff.contMDiff

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ExponentialSmooth.Constructions.Exponential
