import OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry

/-! # Geometric Generic Fiber -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.GeometricGenericFiber

noncomputable section

/-! # The original geometric generic fiber and its map to the integral model

The geometric fiber definition is shared with the etale Galois
representation. Its name and defining pullback are unchanged; the geometry
does not require the period-ring constructions used for the representation.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

namespace EtaleGalois

open OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry OAI.NumberTheory.PadicHodge.IntegralComparison.Frobenius.Geometry

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K]

/-- The geometric generic fiber of the actual integral model. -/
abbrev geometricGenericFiber (M : IntegralGeometry.IntegralModel p K) : Scheme.{u} :=
  IntegralComparison.Frobenius.Geometry.geometricFiber (L := AlgebraicClosure K) (((IntegralGeometry.genericFiberFunctor p K).obj M).hom)

end EtaleGalois

open OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry OAI.NumberTheory.PadicHodge.PeriodInvariants.GeometricGenericFiber.EtaleGalois

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [Algebra ℚ_[p] K]
  [FiniteDimensional ℚ_[p] K] (M : IntegralGeometry.IntegralModel p K)

def toGeneric : EtaleGalois.geometricGenericFiber p K M ⟶ IntegralGeometry.genericFiber p K M :=
  pullback.fst ((IntegralGeometry.genericFiberFunctor p K).obj M).hom
    (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))

def toModel : EtaleGalois.geometricGenericFiber p K M ⟶ M.left :=
  toGeneric p K M ≫ pullback.fst M.hom
    (Spec.map (CommRingCat.ofHom (algebraMap (IntegralGeometry.ringOfIntegers p K) K)))

def overModel : Over M.left := Over.mk (toModel p K M)

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.GeometricGenericFiber
