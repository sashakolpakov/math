import OAI.NumberTheory.PadicHodge.PeriodInvariants.CohomologyCoherence
import OAI.NumberTheory.PadicHodge.PeriodInvariants.GeometricGalois
import OAI.NumberTheory.PadicHodge.PeriodInvariants.GeometricGenericFiber
import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineScalars

/-! # Etale Galois -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleGalois

noncomputable section

/-!
# The actual Galois representation on geometric rational pro-étale cohomology

The action is induced by field automorphisms of the scheme-theoretic geometric
fiber and exact transport of sheaves. The group laws are proved from the
cohomological pullback laws. Finite dimensionality and crystallinity are not
assumed or asserted here.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Cohomology OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.Frobenius
  CohomologyCoherence GeometricGalois

variable (p : ℕ) [Fact p.Prime]

section FiberAction

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)

/-- The Galois action over the universe-lifted coefficient field. -/
def geometricCohomologyAction : (L ≃ₐ[K] L) →*
    (IntegralComparison.Cohomology.RationalEllAdicCohomology p (IntegralComparison.Frobenius.Geometry.geometricFiber (L := L) f) n ≃ₗ[IntegralComparison.Cohomology.Coeff.{u} p]
      IntegralComparison.Cohomology.RationalEllAdicCohomology p (IntegralComparison.Frobenius.Geometry.geometricFiber (L := L) f) n) where
  toFun σ := IntegralComparison.Etale.Frobenius.cohomologyPullback p (IntegralComparison.Frobenius.Geometry.geometricFiberIso f σ) n
  map_one' := by
    rw [GeometricGalois.geometricFiberIso_one, CohomologyCoherence.cohomologyPullback_refl]
    rfl
  map_mul' σ τ := by
    rw [GeometricGalois.geometricFiberIso_mul]
    exact (CohomologyCoherence.cohomologyPullback_comp p (IntegralComparison.Frobenius.Geometry.geometricFiberIso f σ) (IntegralComparison.Frobenius.Geometry.geometricFiberIso f τ) n).symm

/-- The same actual action, linear over Q_p. -/
def geometricCohomologyActionQp : (L ≃ₐ[K] L) →*
    (IntegralComparison.Cohomology.RationalEllAdicCohomology p (IntegralComparison.Frobenius.Geometry.geometricFiber (L := L) f) n ≃ₗ[ℚ_[p]]
      IntegralComparison.Cohomology.RationalEllAdicCohomology p (IntegralComparison.Frobenius.Geometry.geometricFiber (L := L) f) n) where
  toFun σ := (geometricCohomologyAction p f n σ).restrictScalars ℚ_[p]
  map_one' := by
    rw [map_one]
    rfl
  map_mul' σ τ := by
    rw [map_mul]
    rfl

def geometricCohomologyRepresentation : Representation ℚ_[p] (L ≃ₐ[K] L)
    (IntegralComparison.Cohomology.RationalEllAdicCohomology p (IntegralComparison.Frobenius.Geometry.geometricFiber (L := L) f) n) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (geometricCohomologyActionQp p f n)

end FiberAction

open OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineScalars

variable (K : Type u) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

abbrev geometricEtaleCohomology (M : IntegralGeometry.IntegralModel p K) (n : ℕ) :=
  IntegralComparison.Cohomology.RationalEllAdicCohomology p (GeometricGenericFiber.EtaleGalois.geometricGenericFiber p K M) n

/-- The actual local Galois representation attached to the integral model. -/
def etaleRepresentation (M : IntegralGeometry.IntegralModel p K) (n : ℕ) :
    Representation ℚ_[p] (CrystallineScalars.LocalGalois K) (geometricEtaleCohomology p K M n) :=
  geometricCohomologyRepresentation p (((IntegralGeometry.genericFiberFunctor p K).obj M).hom) n

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.EtaleGalois
