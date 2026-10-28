import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.AtVariable
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.HypersurfaceRetraction

/-! # Mv Polynomial Relative Line -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MvPolynomialRelativeLine.Construction

noncomputable section

/-! Separating any selected étale polynomial coordinate as a relative affine line. -/

universe u

variable {σ k R : Type u} [Field k] [CommRing R]

abbrev coordinateLineBase (h : σ) := MvPolynomial {j : σ // j ≠ h} k

/-- The chosen variable is the line coordinate, and all others are coefficients. -/
def coordinateLineEquiv (h : σ) : MvPolynomial σ k ≃ₐ[k] Polynomial (coordinateLineBase (k := k) h) :=
  (Coordinate.AtVariable.Construction.separateVariableEquiv h).trans (MvPolynomial.optionEquivLeft k {j : σ // j ≠ h})

theorem coordinateLineEquiv_X (h : σ) :
    coordinateLineEquiv (k := k) h (MvPolynomial.X h) = Polynomial.X := by
  rw [coordinateLineEquiv, AlgEquiv.trans_apply, Coordinate.AtVariable.Construction.separateVariableEquiv_X_self,
    MvPolynomial.optionEquivLeft_X_none]

theorem coordinateLineEquiv_other (h : σ) (j : {j : σ // j ≠ h}) :
    coordinateLineEquiv (k := k) h (MvPolynomial.X j.val) = Polynomial.C (MvPolynomial.X j) := by
  rw [coordinateLineEquiv, AlgEquiv.trans_apply, Coordinate.AtVariable.Construction.separateVariableEquiv_X_ne h j.val j.property,
    MvPolynomial.optionEquivLeft_X_some]

theorem coordinateLineEquiv_symm_X (h : σ) :
    (coordinateLineEquiv (k := k) h).symm Polynomial.X = MvPolynomial.X h := by
  apply (coordinateLineEquiv h).injective
  rw [AlgEquiv.apply_symm_apply, coordinateLineEquiv_X]

theorem coordinateLineEquiv_symm_other (h : σ) (j : {j : σ // j ≠ h}) :
    (coordinateLineEquiv (k := k) h).symm (Polynomial.C (MvPolynomial.X j)) = MvPolynomial.X j.val := by
  apply (coordinateLineEquiv h).injective
  rw [AlgEquiv.apply_symm_apply, coordinateLineEquiv_other]

variable [Algebra (MvPolynomial σ k) R]

def coordinateLineMap (h : σ) : Polynomial (coordinateLineBase (k := k) h) →+* R :=
  (algebraMap (MvPolynomial σ k) R).comp (coordinateLineEquiv h).symm.toRingHom

def coordinateLineBaseMap (h : σ) : coordinateLineBase (k := k) h →+* R :=
  (coordinateLineMap (R := R) h).comp Polynomial.C

theorem coordinateLineMap_X (h : σ) :
    coordinateLineMap (k := k) (R := R) h Polynomial.X =
      algebraMap (MvPolynomial σ k) R (MvPolynomial.X h) := by
  change algebraMap (MvPolynomial σ k) R ((coordinateLineEquiv h).symm Polynomial.X) = _
  rw [coordinateLineEquiv_symm_X]

theorem coordinateLineBaseMap_X (h : σ) (j : {j : σ // j ≠ h}) :
    coordinateLineBaseMap (k := k) (R := R) h (MvPolynomial.X j) =
      algebraMap (MvPolynomial σ k) R (MvPolynomial.X j.val) := by
  change algebraMap (MvPolynomial σ k) R
    ((coordinateLineEquiv h).symm (Polynomial.C (MvPolynomial.X j))) = _
  rw [coordinateLineEquiv_symm_other]

abbrev coordinateLineBaseAlgebra (h : σ) : Algebra (coordinateLineBase (k := k) h) R :=
  (coordinateLineBaseMap h).toAlgebra

abbrev coordinateLineAlgebra (h : σ) : Algebra (Polynomial (coordinateLineBase (k := k) h)) R :=
  (coordinateLineMap h).toAlgebra

attribute [local instance] coordinateLineBaseAlgebra coordinateLineAlgebra

theorem coordinateLine_scalarTower (h : σ) :
    IsScalarTower (coordinateLineBase (k := k) h) (Polynomial (coordinateLineBase (k := k) h)) R :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem coordinateLine_etale [Algebra.Etale (MvPolynomial σ k) R] (h : σ) :
    Algebra.Etale (Polynomial (coordinateLineBase (k := k) h)) R :=
  RingHom.Etale.stableUnderComposition (coordinateLineEquiv h).symm.toRingHom
    (algebraMap (MvPolynomial σ k) R)
    (RingHom.Etale.of_bijective (coordinateLineEquiv h).symm.bijective)
    (RingHom.etale_algebraMap.mpr inferInstance)

variable [Algebra k R] [IsScalarTower k (MvPolynomial σ k) R]

theorem coordinateLineBaseMap_C (h : σ) (c : k) :
    coordinateLineBaseMap (k := k) (R := R) h (MvPolynomial.C c) = algebraMap k R c := by
  change algebraMap (MvPolynomial σ k) R
    ((coordinateLineEquiv h).symm (algebraMap k (Polynomial (coordinateLineBase (k := k) h)) c)) = _
  rw [AlgEquiv.commutes]
  exact (IsScalarTower.algebraMap_apply k (MvPolynomial σ k) R c).symm

theorem coordinateLine_originalScalarTower (h : σ) :
    IsScalarTower k (coordinateLineBase (k := k) h) R := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro c
  exact (coordinateLineBaseMap_C h c).symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MvPolynomialRelativeLine.Construction
