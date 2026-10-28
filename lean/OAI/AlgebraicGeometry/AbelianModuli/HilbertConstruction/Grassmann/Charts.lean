import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quotient.Charts
import Mathlib.RingTheory.Grassmannian

/-! # Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Quotient charts as actual Grassmannian points with finite projective quotients of fixed rank. -/

universe u v

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {k : ℕ}

/-- A quotient chart with a rank-`k` first summand is a Grassmannian point. -/
def Quotient.Charts.QuotientChart.toGrassmannian (c : Quotient.Charts.QuotientChart R (Fin k → R) V) :
    Module.Grassmannian R ((Fin k → R) × V) k where
  toSubmodule := c.val
  finite_quotient := Module.Finite.equiv c.frame
  projective_quotient := Module.Projective.of_equiv c.frame
  rankAtStalk_eq p := by
    have : Nontrivial R := p.nontrivial
    have he := congrFun (Module.rankAtStalk_eq_of_equiv c.frame.symm) p
    exact he.trans (by simp)

/-- The Grassmannian chart on which the first coordinate summand frames the quotient. -/
def Grassmann.Charts.GrassmannChart (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V] (k : ℕ) :=
  {N : Module.Grassmannian R ((Fin k → R) × V) k //
    Function.Bijective (N.toSubmodule.mkQ.comp (LinearMap.inl R (Fin k → R) V))}

/-- The underlying quotient already determines the rank and projectivity conditions on the chart. -/
def Grassmann.Charts.grassmannQuotientChartEquiv : Grassmann.Charts.GrassmannChart R V k ≃ Quotient.Charts.QuotientChart R (Fin k → R) V where
  toFun N := ⟨N.val.toSubmodule, N.property⟩
  invFun c := ⟨c.toGrassmannian, c.property⟩
  left_inv N := by
    apply Subtype.ext
    exact Module.Grassmannian.ext rfl
  right_inv c := rfl

/-- The chart of rank-`k` quotients is parametrized exactly by the corresponding linear maps. -/
def Grassmann.Charts.grassmannChartCoordinates : Grassmann.Charts.GrassmannChart R V k ≃ (V →ₗ[R] (Fin k → R)) :=
  Grassmann.Charts.grassmannQuotientChartEquiv.trans Quotient.Charts.QuotientChart.coordinateEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
