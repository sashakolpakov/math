import OAI.AlgebraicGeometry.Resolution.Blowups.TruncatedTaylor
import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CoefficientStep

/-! # Horizontal Derivation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.HorizontalDerivation.Construction

noncomputable section

/-! Horizontal coefficient derivations on the actual retracted étale line neighborhood. -/

open _root_.Polynomial

universe u

variable (k : Type u) {H R : Type u} [CommRing k] [CommRing H] [CommRing R]
  [Algebra k H] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
  [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]

omit [Algebra.Etale H[X] R] in
theorem etaleLine_polynomial_originalScalarTower : IsScalarTower k H[X] R := by
  apply IsScalarTower.of_algebraMap_eq
  intro x
  calc
    algebraMap k R x = algebraMap H R (algebraMap k H x) := IsScalarTower.algebraMap_apply k H R x
    _ = algebraMap H[X] R (algebraMap H H[X] (algebraMap k H x)) :=
      IsScalarTower.algebraMap_apply H H[X] R _
    _ = algebraMap H[X] R (algebraMap k H[X] x) :=
      congrArg (algebraMap H[X] R) (IsScalarTower.algebraMap_apply k H H[X] x).symm

attribute [local instance] etaleLine_polynomial_originalScalarTower

/-- Extend a coefficient derivation while fixing the line coordinate. -/
def etaleLineHorizontalDerivation (δ : Derivation k H H) : Derivation k R R :=
  Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (R := H[X]) (S := R) (TruncatedTaylor.Construction.polynomialCoefficientDerivation δ)

theorem etaleLineHorizontalDerivation_coefficient (δ : Derivation k H H) (a : H) :
    etaleLineHorizontalDerivation k δ (algebraMap H R a) = algebraMap H R (δ a) := by
  rw [IsScalarTower.algebraMap_apply H H[X] R]
  change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := R) (TruncatedTaylor.Construction.polynomialCoefficientDerivation δ)
    (algebraMap H[X] R (C a)) = _
  rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, TruncatedTaylor.Construction.polynomialCoefficientDerivation_C]
  exact (IsScalarTower.algebraMap_apply H H[X] R (δ a)).symm

theorem etaleLineHorizontalDerivation_coordinate (δ : Derivation k H H) :
    etaleLineHorizontalDerivation k (R := R) δ (algebraMap H[X] R X) = 0 := by
  change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := R) (TruncatedTaylor.Construction.polynomialCoefficientDerivation δ)
    (algebraMap H[X] R X) = 0
  rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap, TruncatedTaylor.Construction.polynomialCoefficientDerivation_X, map_zero]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.HorizontalDerivation.Construction
