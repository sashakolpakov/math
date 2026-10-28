import OAI.NumberTheory.PadicHodge.PeriodInvariants.BigProEtaleSite
import OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius

/-! # Big Etale Cohomology -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.BigEtaleCohomology

noncomputable section

/-!
# Actual rational pro-etale pullback for arbitrary scheme morphisms

The rational coefficient sheaf restricts from the big site to the
existing small-site sheaf. Exact restriction and the proved Ext
comparison identify their cohomology. Postcomposition on the big site
then supplies pullback for every scheme morphism.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology OAI.NumberTheory.PadicHodge.PeriodInvariants.BigProEtaleSite

variable (p : ℕ) [Fact p.Prime] (X : Scheme.{u})

def coefficientSheaf : BigProEtaleSite.BigSheaf p X :=
  ((Over.forget X).sheafPushforwardContinuous (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p))
    (Scheme.proetaleTopology.over X) Scheme.proetaleTopology).obj
      ⟨IntegralComparison.Cohomology.rationalCoefficientPresheaf p,
        .of_le Scheme.proetaleTopology_le_fpqcTopology (IntegralComparison.Cohomology.rationalCoefficientPresheaf_isSheaf p)⟩

abbrev Cohomology (n : ℕ) := Abelian.Ext.{u + 2} (BigProEtaleSite.constantUnit p X) (coefficientSheaf p X) n

def coefficientComparison : (BigProEtaleSite.restriction p X).obj (coefficientSheaf p X) ≅ IntegralComparison.Cohomology.rationalCoefficientSheaf p X :=
  Iso.refl _

def constantComparison : (BigProEtaleSite.restriction p X).obj (BigProEtaleSite.constantUnit p X) ≅ IntegralComparison.Cohomology.constantUnitSheaf p X :=
  ((Scheme.ProEt.forget X).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) (Scheme.ProEt.topology X)
    (Scheme.proetaleTopology.over X)).symm.app
      ((Functor.const _).obj (ModuleCat.of (IntegralComparison.Cohomology.Coeff.{u} p) (IntegralComparison.Cohomology.Coeff.{u} p)))

def comparison (n : ℕ) : Cohomology p X n →ₗ[IntegralComparison.Cohomology.Coeff.{u} p] IntegralComparison.Cohomology.RationalEllAdicCohomology p X n :=
  (IntegralComparison.Etale.Frobenius.extIsoCongr (IntegralComparison.Cohomology.Coeff.{u} p) (constantComparison p X)
    (coefficientComparison p X) n).toLinearMap.comp
      ((BigProEtaleSite.restriction p X).mapExtLinearMap (IntegralComparison.Cohomology.Coeff.{u} p) (BigProEtaleSite.constantUnit p X) (coefficientSheaf p X) n)

theorem comparison_bijective (n : ℕ) : Function.Bijective (comparison p X n) :=
  (IntegralComparison.Etale.Frobenius.extIsoCongr (IntegralComparison.Cohomology.Coeff.{u} p) (constantComparison p X)
    (coefficientComparison p X) n).bijective.comp
      (BigProEtaleSite.mapExt_bijective p X (coefficientSheaf p X) n)

def comparisonEquiv (n : ℕ) : Cohomology p X n ≃ₗ[IntegralComparison.Cohomology.Coeff.{u} p] IntegralComparison.Cohomology.RationalEllAdicCohomology p X n :=
  LinearEquiv.ofBijective (comparison p X n) (comparison_bijective p X n)

variable {X} {Y : Scheme.{u}} (g : X ⟶ Y)

abbrev pullbackFunctor : BigProEtaleSite.BigSheaf p Y ⥤ BigProEtaleSite.BigSheaf p X :=
  (Over.map g).sheafPushforwardContinuous (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p))
    (Scheme.proetaleTopology.over X) (Scheme.proetaleTopology.over Y)

instance pullbackFunctor_additive : (pullbackFunctor p g).Additive where
  map_add := by intros; rfl

instance pullbackFunctor_linear : (pullbackFunctor p g).Linear (IntegralComparison.Cohomology.Coeff.{u} p) where
  map_smul := by intros; rfl

instance pullbackFunctor_leftAdjoint : (pullbackFunctor p g).IsLeftAdjoint :=
  ((Over.map g).sheafAdjunctionCocontinuous (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p))
    (Scheme.proetaleTopology.over X) (Scheme.proetaleTopology.over Y)).isLeftAdjoint

instance pullbackFunctor_preservesFiniteLimits : PreservesFiniteLimits (pullbackFunctor p g) := by
  infer_instance

instance pullbackFunctor_preservesFiniteColimits : PreservesFiniteColimits (pullbackFunctor p g) := by
  infer_instance

def coefficientTransport : (pullbackFunctor p g).obj (coefficientSheaf p Y) ≅ coefficientSheaf p X :=
  Iso.refl _

def constantTransport : (pullbackFunctor p g).obj (BigProEtaleSite.constantUnit p Y) ≅ BigProEtaleSite.constantUnit p X :=
  ((Over.map g).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} (IntegralComparison.Cohomology.Coeff.{u} p)) (Scheme.proetaleTopology.over X)
    (Scheme.proetaleTopology.over Y)).symm.app
      ((Functor.const _).obj (ModuleCat.of (IntegralComparison.Cohomology.Coeff.{u} p) (IntegralComparison.Cohomology.Coeff.{u} p)))

def bigPullback (n : ℕ) : Cohomology p Y n →ₗ[IntegralComparison.Cohomology.Coeff.{u} p] Cohomology p X n :=
  (IntegralComparison.Etale.Frobenius.extIsoCongr (IntegralComparison.Cohomology.Coeff.{u} p) (constantTransport p g)
    (coefficientTransport p g) n).toLinearMap.comp
      ((pullbackFunctor p g).mapExtLinearMap (IntegralComparison.Cohomology.Coeff.{u} p) (BigProEtaleSite.constantUnit p Y) (coefficientSheaf p Y) n)

def pullback (n : ℕ) : IntegralComparison.Cohomology.RationalEllAdicCohomology p Y n →ₗ[IntegralComparison.Cohomology.Coeff.{u} p] IntegralComparison.Cohomology.RationalEllAdicCohomology p X n :=
  (comparisonEquiv p X n).toLinearMap.comp
    ((bigPullback p g n).comp (comparisonEquiv p Y n).symm.toLinearMap)

def pullbackQp (n : ℕ) : IntegralComparison.Cohomology.RationalEllAdicCohomology p Y n →ₗ[ℚ_[p]] IntegralComparison.Cohomology.RationalEllAdicCohomology p X n :=
  (pullback p g n).restrictScalars ℚ_[p]

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.BigEtaleCohomology
