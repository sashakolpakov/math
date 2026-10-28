import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.MonomialBasis
import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Coordinate Basis -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert

noncomputable section

/-! Canonical finite monomial coordinates on homogeneous polynomial pieces.
The index sets are independent of the coefficient ring. -/

open _root_.MvPolynomial _root_.Module

universe u

abbrev DegreeMonomials (n d : ℕ) := {a : Fin (n + 1) →₀ ℕ // a.degree = d}

def degreeSpaceSupportedEquiv (R : Type u) [CommRing R] (n d : ℕ) :
    Hilbert.Polynomial.GradedHilbert.grading R n d ≃ₗ[R] restrictSupport R {a : Fin (n + 1) →₀ ℕ | a.degree = d} where
  toFun f := ⟨f.val, (Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support f.val d).mp f.property⟩
  invFun f := ⟨f.val, (Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support f.val d).mpr f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def degreeMonomialBasis (R : Type u) [CommRing R] (n d : ℕ) :
    Basis (DegreeMonomials n d) R (Hilbert.Polynomial.GradedHilbert.grading R n d) :=
  (basisRestrictSupport R {a : Fin (n + 1) →₀ ℕ | a.degree = d}).map
    (degreeSpaceSupportedEquiv R n d).symm

instance degreeMonomials_finite (n d : ℕ) : Finite (DegreeMonomials n d) :=
  Module.Finite.finite_basis (degreeMonomialBasis ℚ n d)

abbrev DegreeIndex (n d : ℕ) := ULift.{u} (DegreeMonomials n d)

instance degreeIndex_fintype (n d : ℕ) : Fintype (DegreeIndex.{u} n d) := Fintype.ofFinite _

def coordinateDegreeBasis (R : Type u) [CommRing R] (n d : ℕ) :
    Basis (DegreeIndex.{u} n d) R (Hilbert.Polynomial.GradedHilbert.grading R n d) :=
  (degreeMonomialBasis R n d).reindex Equiv.ulift.symm

theorem degreeMonomialBasis_val (R : Type u) [CommRing R] (n d : ℕ) (a : DegreeMonomials n d) :
    (degreeMonomialBasis R n d a).val = monomial a.val (1 : R) := by
  change ((basisRestrictSupport R {a : Fin (n + 1) →₀ ℕ | a.degree = d}) a).val = _
  change ((basisRestrictSupport R {a : Fin (n + 1) →₀ ℕ | a.degree = d}).repr.symm
    (Finsupp.single a 1)).val = _
  change AddMonoidAlgebra.ofCoeff
    (((Finsupp.supportedEquivFinsupp (R := R) {a : Fin (n + 1) →₀ ℕ | a.degree = d}).symm
      (Finsupp.single a (1 : R))).val) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

theorem coordinateDegreeBasis_val (R : Type u) [CommRing R] (n d : ℕ) (a : DegreeIndex.{u} n d) :
    (coordinateDegreeBasis R n d a).val = monomial a.down.val (1 : R) := by
  rw [coordinateDegreeBasis, Basis.reindex_apply]
  exact degreeMonomialBasis_val R n d a.down

theorem degreeMonomialBasis_repr (R : Type u) [CommRing R] (n d : ℕ)
    (f : Hilbert.Polynomial.GradedHilbert.grading R n d) (a : DegreeMonomials n d) :
    (degreeMonomialBasis R n d).repr f a = AddMonoidAlgebra.coeff f.val a.val := rfl

theorem coordinateDegreeBasis_repr (R : Type u) [CommRing R] (n d : ℕ)
    (f : Hilbert.Polynomial.GradedHilbert.grading R n d) (a : DegreeIndex.{u} n d) :
    (coordinateDegreeBasis R n d).repr f a = AddMonoidAlgebra.coeff f.val a.down.val := by
  rw [coordinateDegreeBasis, Basis.repr_reindex_apply]
  exact degreeMonomialBasis_repr R n d f a.down

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CoordinateBasis.GradedHilbert
