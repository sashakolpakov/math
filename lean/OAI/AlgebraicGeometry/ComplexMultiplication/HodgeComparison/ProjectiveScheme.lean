import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveGluing
import OAI.AlgebraicGeometry.Albanese.Construction.ProjectiveCover
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveVarietyRealization

/-! # Projective Scheme -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction

noncomputable section

/-! The genuine projective scheme and its smooth projective embedding maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.Manifold ContDiff

/-- The zero homogeneous prime is the generic point of ordinary projective space. -/
def projectiveGenericPoint (n : ℕ) : Foundations.Scheme.ProjectiveSpace.projectiveSpace n where
  asHomogeneousIdeal := ⊥
  isPrime := by
    rw [HomogeneousIdeal.toIdeal_bot]
    infer_instance
  not_irrelevant_le := by
    intro h
    have hX : MvPolynomial.X (0 : Fin (n + 1)) ∈ HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) :=
      HomogeneousIdeal.mem_irrelevant_of_mem (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (by decide : 0 < 1)
        (MvPolynomial.isHomogeneous_X ℂ (0 : Fin (n + 1)))
    have hz : MvPolynomial.X (0 : Fin (n + 1)) ∈ (⊥ : Ideal (Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n)) := h hX
    exact MvPolynomial.X_ne_zero _ (Ideal.mem_bot.mp hz)

theorem projectiveGenericPoint_dense (n : ℕ) :
    closure ({projectiveGenericPoint n} : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  apply (ProjectiveSpectrum.le_iff_mem_closure (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (projectiveGenericPoint n) x).mp
  change (⊥ : HomogeneousIdeal (Foundations.Scheme.ProjectiveSpace.projectiveGrading n)) ≤ x.asHomogeneousIdeal
  exact bot_le

theorem projectiveScheme_irreducible (n : ℕ) : IrreducibleSpace (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := by
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (Foundations.Scheme.ProjectiveSpace.projectiveSpace n))
  rw [← projectiveGenericPoint_dense n]
  exact isIrreducible_singleton.closure

theorem projectiveScheme_integral (n : ℕ) : IsIntegral (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := by
  have : IrreducibleSpace (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := projectiveScheme_irreducible n
  have : Smooth (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) := Albanese.Construction.ProjectiveCover.projectiveSpace_smooth n
  have : IsReduced (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Standard projective space as the existing genuine variety bundle. -/
def projectiveSpaceVariety (n : ℕ) : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety :=
  Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.ofClosedImmersion (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n) n (𝟙 _)
    inferInstance (Category.id_comp _) (Albanese.Construction.ProjectiveCover.projectiveSpace_smooth n) (projectiveScheme_integral n)

def projectiveEmbeddingMap (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    V.toOver ⟶ (projectiveSpaceVariety V.ambientDimension).toOver :=
  V.presentation.projective.toOverHom

theorem projectiveEmbeddingMap_holomorphic (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    ContMDiff 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, (projectiveSpaceVariety V.ambientDimension).analyticModel) ∞
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (projectiveEmbeddingMap V)) := by
  have : IsIntegral V.toOver.left := V.property
  have : Smooth V.toOver.hom := V.presentation.smooth
  have : IsIntegral (projectiveSpaceVariety V.ambientDimension).toOver.left :=
    (projectiveSpaceVariety V.ambientDimension).property
  have : Smooth (projectiveSpaceVariety V.ambientDimension).toOver.hom :=
    (projectiveSpaceVariety V.ambientDimension).presentation.smooth
  exact ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map (projectiveEmbeddingMap V) ∞

theorem projectiveEmbeddingMap_injective_differential (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x : V.analyticSpace) :
    Function.Injective (mfderiv 𝓘(ℂ, V.analyticModel)
      𝓘(ℂ, (projectiveSpaceVariety V.ambientDimension).analyticModel)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (projectiveEmbeddingMap V)) x) := by
  have : IsIntegral V.toOver.left := V.property
  have : Smooth V.toOver.hom := V.presentation.smooth
  have : IsIntegral (projectiveSpaceVariety V.ambientDimension).toOver.left :=
    (projectiveSpaceVariety V.ambientDimension).property
  have : Smooth (projectiveSpaceVariety V.ambientDimension).toOver.hom :=
    (projectiveSpaceVariety V.ambientDimension).presentation.smooth
  have : IsClosedImmersion (projectiveEmbeddingMap V).left := V.presentation.projective.closedImmersion
  exact ComplexPoints.Analytic.IntrinsicSmoothClosedImmersion.mfderiv_nativeScheme_closedImmersion_injective (projectiveEmbeddingMap V) x

def projectiveEmbeddingCoordinates (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    V.analyticSpace → Projectivization ℂ (Fin (V.ambientDimension + 1) → ℂ) :=
  (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph V.ambientDimension).symm ∘
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (projectiveEmbeddingMap V)

theorem projectiveEmbeddingCoordinates_continuous (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Continuous (projectiveEmbeddingCoordinates V) :=
  (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph V.ambientDimension).symm.continuous.comp
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map (projectiveEmbeddingMap V))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction
