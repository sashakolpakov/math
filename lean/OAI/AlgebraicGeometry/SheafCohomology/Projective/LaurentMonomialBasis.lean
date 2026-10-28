/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentExponentLocalization
import Mathlib.Algebra.MonoidAlgebra.Module

/-! # Laurent Monomial Basis -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentMonomialBasis.MvPolynomial

open _root_.MvPolynomial

/-!
# Laurent monomial bases

The localization of a multivariable polynomial ring away from a monomial is canonically the
additive monoid algebra on the corresponding allowed Laurent exponents. Transporting the standard
monoid-algebra basis gives Laurent monomial coordinates on the localization.
-/

universe u v

variable (R : Type u) [CommSemiring R] {σ : Type v}

/-- The canonical ring equivalence from a monomial localization to the additive monoid algebra on
the allowed Laurent exponents. -/
noncomputable def laurentMonomialRingEquiv (m : σ →₀ ℕ) :
    Localization.Away (monomial m (1 : R)) ≃+*
      AddMonoidAlgebra R (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m) := by
  letI := (AddMonoidAlgebra.mapDomainRingHom R
    (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap m).toAddMonoidHom).toAlgebra
  letI : IsLocalization.Away (monomial m (1 : R))
      (AddMonoidAlgebra R (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m)) :=
    AddMonoidAlgebraLocalization.AddMonoidAlgebra.isLocalizationAway_of_isLocalizationMap (R := R)
      (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap m)
  exact (Localization.algEquiv (Submonoid.powers (monomial m (1 : R)))
    (AddMonoidAlgebra R (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m))).toRingEquiv

/-- The Laurent-monomial equivalence sends a polynomial to the same polynomial with its natural
exponents regarded as allowed integer exponents. -/
theorem laurentMonomialRingEquiv_algebraMap (m : σ →₀ ℕ) (p : MvPolynomial σ R) :
    laurentMonomialRingEquiv R m
        (algebraMap (MvPolynomial σ R) (Localization.Away (monomial m (1 : R))) p) =
      AddMonoidAlgebra.mapDomain (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap m).toAddMonoidHom p := by
  let := (AddMonoidAlgebra.mapDomainRingHom R
    (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap m).toAddMonoidHom).toAlgebra
  let : IsLocalization.Away (monomial m (1 : R))
      (AddMonoidAlgebra R (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m)) :=
    AddMonoidAlgebraLocalization.AddMonoidAlgebra.isLocalizationAway_of_isLocalizationMap (R := R)
      (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap m)
  change (Localization.algEquiv (Submonoid.powers (monomial m (1 : R)))
    (AddMonoidAlgebra R (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m)))
      (algebraMap (MvPolynomial σ R) (Localization.Away (monomial m (1 : R))) p) = _
  exact (Localization.algEquiv (Submonoid.powers (monomial m (1 : R)))
    (AddMonoidAlgebra R (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m))).commutes p

/-- The Laurent-monomial equivalence respects the coefficient-ring embeddings. -/
theorem laurentMonomialRingEquiv_algebraMap_coeff (m : σ →₀ ℕ) (r : R) :
    laurentMonomialRingEquiv R m
        (algebraMap R (Localization.Away (monomial m (1 : R))) r) =
      algebraMap R (AddMonoidAlgebra R (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m)) r := by
  have hsource : algebraMap R (Localization.Away (monomial m (1 : R))) r =
      algebraMap (MvPolynomial σ R) (Localization.Away (monomial m (1 : R)))
        (MvPolynomial.C r) := by
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial σ R)]
    rfl
  have htarget :
      AddMonoidAlgebra.mapDomain (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap m).toAddMonoidHom
          (MvPolynomial.C r) =
        algebraMap R (AddMonoidAlgebra R (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m)) r := by
    change AddMonoidAlgebra.mapDomain (LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap m).toAddMonoidHom
      (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 r
    rw [AddMonoidAlgebra.mapDomain_single]
    congr 1
  rw [hsource]
  exact (laurentMonomialRingEquiv_algebraMap R m (MvPolynomial.C r)).trans htarget

/-- The `R`-linear equivalence underlying `laurentMonomialRingEquiv`. -/
noncomputable def laurentMonomialLinearEquiv (m : σ →₀ ℕ) :
    Localization.Away (monomial m (1 : R)) ≃ₗ[R]
      AddMonoidAlgebra R (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m) :=
  { laurentMonomialRingEquiv R m with
    map_smul' := by
      intro r x
      simp only [Algebra.smul_def, RingHom.id_apply]
      change laurentMonomialRingEquiv R m
          (algebraMap R (Localization.Away (monomial m (1 : R))) r * x) =
        algebraMap R (AddMonoidAlgebra R (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m)) r *
          laurentMonomialRingEquiv R m x
      rw [map_mul, laurentMonomialRingEquiv_algebraMap_coeff] }

/-- The basis of a monomial localization indexed by its allowed Laurent exponents. -/
noncomputable def laurentMonomialBasis (m : σ →₀ ℕ) :
    Module.Basis (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m) R
      (Localization.Away (monomial m (1 : R))) :=
  (AddMonoidAlgebra.basis (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m) R).map
    (laurentMonomialLinearEquiv R m).symm

@[simp]
theorem laurentMonomialRingEquiv_basis_apply (m : σ →₀ ℕ)
    (e : LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m) :
    laurentMonomialRingEquiv R m (laurentMonomialBasis R m e) =
      AddMonoidAlgebra.single e 1 := by
  change laurentMonomialLinearEquiv R m
      ((laurentMonomialLinearEquiv R m).symm
        (AddMonoidAlgebra.basis (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid m) R e)) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentMonomialBasis.MvPolynomial
