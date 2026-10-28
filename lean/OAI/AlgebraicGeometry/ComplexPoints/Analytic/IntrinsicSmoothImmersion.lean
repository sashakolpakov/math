import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SchemeImmersionPointTopology
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicOpenDifferential

/-! # Intrinsic Smooth Immersion -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothImmersion

noncomputable section

/-!
# Native analytic differentials of actual algebraic immersions

The genuine coborder factorization expresses an algebraic immersion as a
closed immersion followed by an open immersion. The open intermediate scheme
inherits integrality and smoothness from the ambient scheme. The previously
proved native differential results for both factors then give injectivity
for the original immersion, including inclusions of smooth integral strata.
-/

open scoped ContDiff _root_.Manifold _root_.Topology
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}

/-- The actual open intermediate scheme is nonempty whenever the source of
the immersion is nonempty, since the closed factor maps into it. -/
instance nonempty_immersionOpenTarget (φ : X ⟶ Y) [IsImmersion φ.left]
    [Nonempty X.left] : Nonempty (SchemePointHomeomorphs.schemeComplexPoints.immersionOpenTarget φ).left :=
  Nonempty.map (SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ).left inferInstance

/-- The genuine coborder open in an integral ambient scheme is integral when
the source is nonempty. -/
instance isIntegral_immersionOpenTarget (φ : X ⟶ Y) [IsImmersion φ.left]
    [Nonempty X.left] [IsIntegral Y.left] :
    IsIntegral (SchemePointHomeomorphs.schemeComplexPoints.immersionOpenTarget φ).left :=
  isIntegral_of_isOpenImmersion (SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ).left

/-- Smoothness of the coborder open is inherited through its actual open
immersion into the ambient smooth complex scheme. -/
instance smooth_immersionOpenTarget (φ : X ⟶ Y) [IsImmersion φ.left]
    [Smooth Y.hom] : Smooth (SchemePointHomeomorphs.schemeComplexPoints.immersionOpenTarget φ).hom := by
  change Smooth (φ.left.coborderRange.ι ≫ Y.hom)
  infer_instance

variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)

/-- Every genuine immersion of smooth integral complex schemes has injective
complex differential on the constructed native point manifolds. -/
theorem mfderiv_nativeScheme_immersion_injective (φ : X ⟶ Y)
    [IsImmersion φ.left] (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Function.Injective
      (mfderiv (𝓘(ℂ, ModelX)) (𝓘(ℂ, ModelY)) (SchemePointHomeomorphs.schemeComplexPoints.map φ) x) := by
  rw [SchemePointHomeomorphs.schemeComplexPoints.map_immersion_factorization φ]
  rw [mfderiv_comp x
    ((IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ) 1).mdifferentiableAt
      one_ne_zero)
    ((IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ) 1).mdifferentiableAt
      one_ne_zero)]
  exact (IntrinsicOpenDifferential.mfderiv_nativeScheme_openImmersion_bijective
      (SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ)
      (SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ) x)).1.comp
    (IntrinsicSmoothClosedImmersion.mfderiv_nativeScheme_closedImmersion_injective
      (SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ) x)

/-- The same actual algebraic immersion has injective differential on the
underlying real smooth manifolds used for differential forms and integration. -/
theorem real_mfderiv_nativeScheme_immersion_injective (φ : X ⟶ Y)
    [IsImmersion φ.left] (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    Function.Injective
      (mfderiv (𝓘(ℝ, ModelX)) (𝓘(ℝ, ModelY)) (SchemePointHomeomorphs.schemeComplexPoints.map φ) x) := by
  rw [SchemePointHomeomorphs.schemeComplexPoints.map_immersion_factorization φ]
  rw [mfderiv_comp x
    ((IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map (SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ) 1).mdifferentiableAt
      one_ne_zero)
    ((IntrinsicSmoothSchemeMaps.real_contMDiff_nativeScheme_map (SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ) 1).mdifferentiableAt
      one_ne_zero)]
  exact (IntrinsicOpenDifferential.real_mfderiv_nativeScheme_openImmersion_bijective
      (SchemePointHomeomorphs.schemeComplexPoints.immersionOpenFactor φ)
      (SchemePointHomeomorphs.schemeComplexPoints.map (SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ) x)).1.comp
    (IntrinsicSmoothClosedImmersion.real_mfderiv_nativeScheme_closedImmersion_injective
      (SchemePointHomeomorphs.schemeComplexPoints.immersionClosedFactor φ) x)

/-- An actual algebraic immersion realizes as a locally closed embedding of
native complex point spaces with injective complex differential everywhere. -/
theorem nativeScheme_immersion_embedding_and_injective_differential
    (φ : X ⟶ Y) [IsImmersion φ.left] :
    Topology.IsEmbedding (SchemePointHomeomorphs.schemeComplexPoints.map φ) ∧
      IsLocallyClosed (Set.range (SchemePointHomeomorphs.schemeComplexPoints.map φ)) ∧
      ∀ x : SchemePointHomeomorphs.schemeComplexPoints X,
        Function.Injective
          (mfderiv (𝓘(ℂ, ModelX)) (𝓘(ℂ, ModelY)) (SchemePointHomeomorphs.schemeComplexPoints.map φ) x) :=
  ⟨SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion φ,
    SchemePointHomeomorphs.schemeComplexPoints.isLocallyClosed_range_map_of_isImmersion φ,
    mfderiv_nativeScheme_immersion_injective φ⟩

/-- The underlying real realization is likewise a locally closed embedding
with injective real manifold differential. -/
theorem nativeScheme_immersion_embedding_and_injective_real_differential
    (φ : X ⟶ Y) [IsImmersion φ.left] :
    Topology.IsEmbedding (SchemePointHomeomorphs.schemeComplexPoints.map φ) ∧
      IsLocallyClosed (Set.range (SchemePointHomeomorphs.schemeComplexPoints.map φ)) ∧
      ∀ x : SchemePointHomeomorphs.schemeComplexPoints X,
        Function.Injective
          (mfderiv (𝓘(ℝ, ModelX)) (𝓘(ℝ, ModelY)) (SchemePointHomeomorphs.schemeComplexPoints.map φ) x) :=
  ⟨SchemePointHomeomorphs.schemeComplexPoints.isEmbedding_map_of_isImmersion φ,
    SchemePointHomeomorphs.schemeComplexPoints.isLocallyClosed_range_map_of_isImmersion φ,
    real_mfderiv_nativeScheme_immersion_injective φ⟩

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothImmersion
