import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.AlgebraicSmoothCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.BettiProduct
import OAI.AlgebraicGeometry.Comparison.Betti.PositiveProjectiveAmbient

/-! # Cech Betti Equivalence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CechBettiEquivalence

noncomputable section

/-! A genuine projective affine cover on which the actual algebraic
Čech-to-Betti product comparison is a linear equivalence. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance integral : IsIntegral V.toOver.left := V.property
local instance smooth : Smooth V.toOver.hom := V.presentation.smooth
local instance proper : IsProper V.toOver.hom := V.presentation.projective.isProper

theorem positiveEmbeddingExists :
    ∃ (n : ℕ) (i : V.toOver.left ⟶ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpace (n + 1)),
      IsClosedImmersion i ∧ i ≫ AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1) = V.toOver.hom :=
  AlgebraicGeometry.Comparison.Betti.PositiveProjectiveAmbient.exists_positive_projective_embedding V.presentation.projective

def ambientDimension : ℕ := (positiveEmbeddingExists V).choose

def embedding : V.toOver ⟶ Over.mk (AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (ambientDimension V + 1)) :=
  Over.homMk (positiveEmbeddingExists V).choose_spec.choose
    (positiveEmbeddingExists V).choose_spec.choose_spec.2

instance embedding_closed : IsClosedImmersion (embedding V).left :=
  (positiveEmbeddingExists V).choose_spec.choose_spec.1

def cover : Fin (ambientDimension V + 2) → V.toOver.left.Opens :=
  fun i => (embedding V).left ⁻¹ᵁ AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen (ambientDimension V + 1) i

theorem cover_affine (i : Fin (ambientDimension V + 2)) : IsAffineOpen (cover V i) :=
  AlgebraicGeometry.Comparison.Betti.EmbeddedHolomorphicAcyclicity.embeddedProjectiveCoordinateCover_affine
    (ambientDimension V + 1) V.toOver (embedding V) i

theorem cover_covers : ⨆ i, cover V i = ⊤ :=
  AlgebraicGeometry.Comparison.Betti.EmbeddedHolomorphicAcyclicity.embeddedProjectiveCoordinateCover_covers
    (ambientDimension V + 1) V.toOver (embedding V)

theorem algebraicComparison_bijective (n : ℕ) :
    Function.Bijective (Cech.BettiProduct.algebraicComparison V (cover V) (cover_covers V) n) := by
  have hq : QuasiIso (AlgebraicSmoothCechProduct.totalMap V.toOver
      (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver (cover V))) :=
    AlgebraicSmoothCech.native_map_quasiIso V.toOver
      (ambientDimension V) (embedding V)
  exact (Cech.BettiProduct.smoothComparison V (cover V) (cover_covers V) n).bijective.comp
    (ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap
      (AlgebraicSmoothCechProduct.totalMap V.toOver
        (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver (cover V))) n))

def algebraicEquiv (n : ℕ) :
    (RationalDeRham.TotalCup.Cech.total ℂ V.toOver
      (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver (cover V))).homology n ≃ₗ[ℂ]
        V.complexCohomology n :=
  LinearEquiv.ofBijective
    (Cech.BettiProduct.algebraicComparison V (cover V) (cover_covers V) n)
    (algebraicComparison_bijective V n)

theorem algebraicEquiv_cup (p q : ℕ)
    (a : (RationalDeRham.TotalCup.Cech.total ℂ V.toOver
      (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver (cover V))).homology p)
    (b : (RationalDeRham.TotalCup.Cech.total ℂ V.toOver
      (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver (cover V))).homology q) :
    algebraicEquiv V (p + q)
        (RationalDeRham.CohomologyCup.Cech.cohomologyCup ℂ V.toOver
          (IntegralComparison.Smooth.CechAnalyticCoordinates.GlobalComparison.nerve V.toOver (cover V)) p q a b) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (AlgebraicGeometry.Betti.Scheme.schemePointSpace V.toOver) p q
        (algebraicEquiv V p a) (algebraicEquiv V q b) :=
  Cech.BettiProduct.algebraicComparison_cup V (cover V) (cover_covers V) p q a b

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.CechBettiEquivalence
