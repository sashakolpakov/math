import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Coordinate Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateReindex

noncomputable section

/-!
# IntegralComparison: étale polynomial coordinates can be reindexed across universes
-/

universe u v w z

variable (R : Type u) (A : Type v) (ι : Type w) (σ : Type z)
  [CommRing R] [CommRing A] [Algebra R A] [Algebra (MvPolynomial ι R) A]
  [IsScalarTower R (MvPolynomial ι R) A] [Algebra.Etale (MvPolynomial ι R) A]
  (e : ι ≃ σ)

@[instance_reducible]
def algebra : Algebra (MvPolynomial σ R) A :=
  ((algebraMap (MvPolynomial ι R) A).comp (MvPolynomial.renameEquiv R e.symm).toRingHom).toAlgebra

omit [Algebra.Etale (MvPolynomial ι R) A] in
theorem scalarTower : letI := algebra R A ι σ e
    IsScalarTower R (MvPolynomial σ R) A := by
  let := algebra R A ι σ e
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap R A r = algebraMap (MvPolynomial ι R) A
    ((MvPolynomial.renameEquiv R e.symm) (algebraMap R (MvPolynomial σ R) r))
  rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

omit [Algebra R A] [IsScalarTower R (MvPolynomial ι R) A] in
theorem etale : letI := algebra R A ι σ e
    Algebra.Etale (MvPolynomial σ R) A := by
  let := algebra R A ι σ e
  let : Algebra (MvPolynomial σ R) (MvPolynomial ι R) :=
    (MvPolynomial.renameEquiv R e.symm).toRingHom.toAlgebra
  let : IsScalarTower (MvPolynomial σ R) (MvPolynomial ι R) A :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.Etale (MvPolynomial σ R) (MvPolynomial ι R) :=
    RingHom.etale_algebraMap.mp (RingHom.Etale.of_bijective (MvPolynomial.renameEquiv R e.symm).bijective)
  exact Algebra.Etale.comp (MvPolynomial σ R) (MvPolynomial ι R) A

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Etale.CoordinateReindex
