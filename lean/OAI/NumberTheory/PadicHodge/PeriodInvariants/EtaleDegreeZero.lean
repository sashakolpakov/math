import OAI.NumberTheory.PadicHodge.PeriodInvariants.DegreeZeroSections
import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteContinuousSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology

/-! # Etale Degree Zero -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleDegreeZero

noncomputable section

/-!
# Finiteness of actual rational pro-etale cohomology in degree zero

The terminal pro-etale object identifies degree-zero Ext with continuous
coefficient sections on the scheme. For a noetherian scheme, the proved
generic-point evaluation bound gives finite-dimensionality over Q_p.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite _root_.TopologicalSpace

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology

def identityTerminal (X : Scheme.{u}) : IsTerminal (Scheme.ProEt.mk (𝟙 X)) :=
  IsTerminal.ofUniqueHom
    (fun U => MorphismProperty.Over.homMk U.hom (Category.comp_id U.hom))
    (fun U f => by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id f.left).symm.trans (MorphismProperty.Over.w f))

variable (p : ℕ) [Fact p.Prime] (X : Scheme.{u})

def sectionsEquiv : IntegralComparison.Cohomology.RationalEllAdicCohomology p X 0 ≃ₗ[IntegralComparison.Cohomology.Coeff.{u} p] C(X, IntegralComparison.Cohomology.Coeff.{u} p) :=
  DegreeZeroSections.degreeZeroEquiv (Scheme.ProEt.topology X) (IntegralComparison.Cohomology.Coeff.{u} p)
    (identityTerminal X) (IntegralComparison.Cohomology.rationalCoefficientSheaf p X)

def sectionsEquivQp : IntegralComparison.Cohomology.RationalEllAdicCohomology p X 0 ≃ₗ[ℚ_[p]] C(X, IntegralComparison.Cohomology.Coeff.{u} p) where
  toAddEquiv := (sectionsEquiv p X).toAddEquiv
  map_smul' c x := by
    change sectionsEquiv p X ((ULift.up c : IntegralComparison.Cohomology.Coeff.{u} p) • x) =
      (ULift.up c : IntegralComparison.Cohomology.Coeff.{u} p) • sectionsEquiv p X x
    exact (sectionsEquiv p X).map_smul _ _

instance degreeZero_finite [NoetherianSpace X] : FiniteDimensional ℚ_[p] (IntegralComparison.Cohomology.RationalEllAdicCohomology p X 0) := by
  let _ : FiniteDimensional ℚ_[p] (IntegralComparison.Cohomology.Coeff.{u} p) :=
    FiniteDimensional.of_injective (ULift.moduleEquiv : IntegralComparison.Cohomology.Coeff.{u} p ≃ₗ[ℚ_[p]] ℚ_[p]).toLinearMap
      (ULift.moduleEquiv : IntegralComparison.Cohomology.Coeff.{u} p ≃ₗ[ℚ_[p]] ℚ_[p]).injective
  let _ : FiniteDimensional ℚ_[p] C(X, IntegralComparison.Cohomology.Coeff.{u} p) :=
    FiniteContinuousSections.continuousMap_finite ℚ_[p] X (IntegralComparison.Cohomology.Coeff.{u} p)
  exact FiniteDimensional.of_injective (sectionsEquivQp p X).toLinearMap (sectionsEquivQp p X).injective

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleDegreeZero
