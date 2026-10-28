import OAI.AlgebraicGeometry.Picard.Homomorphisms.Polynomial
import Mathlib.RingTheory.Flat.Rank

/-! # Polynomial Rank -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.PolynomialRank

noncomputable section

/-! The exact finite-free rank of the coordinate power map on the affine line. -/

open _root_.Polynomial _root_.Module

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable (R : Type u) [CommRing R] [Nontrivial R] (n : ℕ)

def polynomialExpansionRootBasis (hn : n ≠ 0) :
    Basis (Fin n) R[X] (AdjoinRoot (Polynomial.Construction.expansionPolynomial R n)) :=
  (AdjoinRoot.powerBasisAux' (monic_X_pow_sub_C (X : R[X]) hn)).reindex
    (finCongr natDegree_X_pow_sub_C)

theorem polynomial_expand_finite (hn : n ≠ 0) : (expand R n).toRingHom.Finite := by
  have : Module.Finite R[X] (AdjoinRoot (Polynomial.Construction.expansionPolynomial R n)) :=
    Module.Finite.of_basis (polynomialExpansionRootBasis R n hn)
  have ho : (AdjoinRoot.of (Polynomial.Construction.expansionPolynomial R n)).Finite :=
    RingHom.finite_algebraMap.mpr this
  have hl : (Polynomial.Construction.expansionLift R n).Finite :=
    RingHom.Finite.of_surjective _ (Polynomial.Construction.expansionEquiv R n).surjective
  have hc := hl.comp ho
  simpa only [Polynomial.Construction.expansionLift, AdjoinRoot.lift_comp_of] using hc

theorem polynomial_expand_finrank (hn : n ≠ 0) (x : PrimeSpectrum R[X]) :
    (expand R n).toRingHom.finrank x = n := by
  have : Module.Finite R[X] (AdjoinRoot (Polynomial.Construction.expansionPolynomial R n)) :=
    Module.Finite.of_basis (polynomialExpansionRootBasis R n hn)
  have : Module.Free R[X] (AdjoinRoot (Polynomial.Construction.expansionPolynomial R n)) :=
    Module.Free.of_basis (polynomialExpansionRootBasis R n hn)
  have ho : (AdjoinRoot.of (Polynomial.Construction.expansionPolynomial R n)).Finite :=
    RingHom.finite_algebraMap.mpr inferInstance
  have hflat : (AdjoinRoot.of (Polynomial.Construction.expansionPolynomial R n)).Flat :=
    RingHom.flat_algebraMap_iff.mpr inferInstance
  have h := RingHom.finrank_comp_left_of_bijective
    (AdjoinRoot.of (Polynomial.Construction.expansionPolynomial R n)) (Polynomial.Construction.expansionLift R n)
    (Polynomial.Construction.expansionEquiv R n).bijective ho hflat x
  simp only [Polynomial.Construction.expansionLift, AdjoinRoot.lift_comp_of] at h
  rw [h]
  change (algebraMap R[X] (AdjoinRoot (Polynomial.Construction.expansionPolynomial R n))).finrank x = n
  rw [RingHom.finrank_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  simpa using Module.finrank_eq_card_basis (polynomialExpansionRootBasis R n hn)

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.PolynomialRank
