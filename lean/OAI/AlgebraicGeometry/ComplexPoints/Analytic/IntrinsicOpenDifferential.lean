import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOpenDifferential
import OAI.AlgebraicGeometry.Foundations.Scheme.AffineOpenSmooth

/-! # Intrinsic Open Differential -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential

noncomputable section

/-!
# Differentials of open immersions on native complex scheme points

Every source point lies in a genuine affine open. The differential of that
affine inclusion and of its composite with the given open immersion are
bijective by the established affine theorem. The manifold chain rule then
proves bijectivity for the original native scheme-point map.
-/

open scoped ContDiff _root_.Manifold _root_.Topology
open _root_.CategoryTheory _root_.AlgebraicGeometry

section DifferentialTransfer

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E₁ E₂ E₃ : Type*}
variable [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
variable [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
variable [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
variable {P M N : Type*}
variable [TopologicalSpace P] [ChartedSpace E₁ P]
variable [TopologicalSpace M] [ChartedSpace E₂ M]
variable [TopologicalSpace N] [ChartedSpace E₃ N]

set_option backward.isDefEq.respectTransparency false in
/-- A bijective differential can be cancelled on the source side of a
composition. This is the actual manifold chain rule followed by cancellation
of a bijective linear map. -/
theorem bijective_mfderiv_of_comp
    (f : M → N) (a : P → M) (x : P)
    (hf : MDifferentiableAt (𝓘(𝕜, E₂)) (𝓘(𝕜, E₃)) f (a x))
    (ha : MDifferentiableAt (𝓘(𝕜, E₁)) (𝓘(𝕜, E₂)) a x)
    (ha_bij : Function.Bijective (mfderiv (𝓘(𝕜, E₁)) (𝓘(𝕜, E₂)) a x))
    (hfa_bij : Function.Bijective
      (mfderiv (𝓘(𝕜, E₁)) (𝓘(𝕜, E₃)) (f ∘ a) x)) :
    Function.Bijective (mfderiv (𝓘(𝕜, E₂)) (𝓘(𝕜, E₃)) f (a x)) := by
  apply (Function.Bijective.of_comp_iff
    (mfderiv (𝓘(𝕜, E₂)) (𝓘(𝕜, E₃)) f (a x)) ha_bij).mp
  change Function.Bijective
    ((mfderiv (𝓘(𝕜, E₂)) (𝓘(𝕜, E₃)) f (a x)).comp
      (mfderiv (𝓘(𝕜, E₁)) (𝓘(𝕜, E₂)) a x))
  rw [← mfderiv_comp x hf ha]
  exact hfa_bij

end DifferentialTransfer

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)

/-- Every actual open immersion between integral smooth complex schemes has
bijective complex differential on the constructed native point manifolds. -/
theorem mfderiv_nativeScheme_openImmersion_bijective (φ : X ⟶ Y)
    [IsOpenImmersion φ.left] (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Function.Bijective
      (mfderiv (𝓘(ℂ, ModelX)) (𝓘(ℂ, ModelY)) (SchemePointHomeomorphs.schemeComplexPoints.map φ) x) := by
  obtain ⟨U, hU, y, hy⟩ := SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift X x
  have hxU : SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ U := by
    have hr : x ∈ Set.range (SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU) := ⟨y, hy⟩
    rwa [SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hr
  let : Nonempty U := ⟨⟨SchemePointHomeomorphs.schemeComplexPoints.underlying x, hxU⟩⟩
  let A := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U
  let : IsDomain A := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain X U
  let : Algebra.Smooth ℂ A := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth X U hU
  let i := SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU
  let : IsOpenImmersion (i ≫ φ).left := by
    change IsOpenImmersion (i.left ≫ φ.left)
    infer_instance
  have hy' : SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i y = x := hy
  rw [← hy']
  apply bijective_mfderiv_of_comp
    (SchemePointHomeomorphs.schemeComplexPoints.map φ) (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) y
    ((IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map φ 1).mdifferentiableAt one_ne_zero)
    ((AffineOpenDifferential.contMDiff_affinePointMap A i 1).mdifferentiableAt one_ne_zero)
    (AffineOpenDifferential.mfderiv_affinePointMap_bijective A i y)
  have hcomp : SchemePointHomeomorphs.schemeComplexPoints.map φ ∘ SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i =
      SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A (i ≫ φ) := by
    funext z
    exact (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp A i φ z).symm
  rw [hcomp]
  exact AffineOpenDifferential.mfderiv_affinePointMap_bijective A (i ≫ φ) y

/-- The same actual open immersion has bijective differential on the
underlying real smooth manifolds. -/
theorem real_mfderiv_nativeScheme_openImmersion_bijective (φ : X ⟶ Y)
    [IsOpenImmersion φ.left] (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Function.Bijective
      (mfderiv (𝓘(ℝ, ModelX)) (𝓘(ℝ, ModelY)) (SchemePointHomeomorphs.schemeComplexPoints.map φ) x) := by
  obtain ⟨U, hU, y, hy⟩ := SchemePointHomeomorphs.schemeComplexPoints.exists_affineOpenPoint_lift X x
  have hxU : SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ U := by
    have hr : x ∈ Set.range (SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X U hU) := ⟨y, hy⟩
    rwa [SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hr
  let : Nonempty U := ⟨⟨SchemePointHomeomorphs.schemeComplexPoints.underlying x, hxU⟩⟩
  let A := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra X U
  let : IsDomain A := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_isDomain X U
  let : Algebra.Smooth ℂ A := SchemePointHomeomorphs.schemeComplexPoints.affineOpenAlgebra_smooth X U hU
  let i := SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X U hU
  let : IsOpenImmersion (i ≫ φ).left := by
    change IsOpenImmersion (i.left ≫ φ.left)
    infer_instance
  have hy' : SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i y = x := hy
  rw [← hy']
  apply bijective_mfderiv_of_comp
    (SchemePointHomeomorphs.schemeComplexPoints.map φ) (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i) y
    ((IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map φ 1).mdifferentiableAt one_ne_zero)
    ((AffineOpenDifferential.real_contMDiff_affinePointMap A i 1).mdifferentiableAt one_ne_zero)
    (AffineOpenDifferential.real_mfderiv_affinePointMap_bijective A i y)
  have hcomp : SchemePointHomeomorphs.schemeComplexPoints.map φ ∘ SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i =
      SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A (i ≫ φ) := by
    funext z
    exact (SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp A i φ z).symm
  rw [hcomp]
  exact AffineOpenDifferential.real_mfderiv_affinePointMap_bijective A (i ≫ φ) y

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential
