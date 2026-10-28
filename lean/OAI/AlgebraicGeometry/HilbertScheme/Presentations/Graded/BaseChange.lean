import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.Quotient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.MonomialBasis
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.GradedAlgebra.TensorProduct
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.RingTheory.Flat.Basic

/-! # Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert

noncomputable section

/-!
Base change of homogeneous coordinate quotients over arbitrary commutative
rings. In each degree the quotient after scalar extension is the tensor
product of the original degree quotient, without a flatness assumption.
-/

open _root_.MvPolynomial TensorProduct

universe u v

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] {n : ℕ}

def gradedCoefficientMap (φ : R →+* S) : Hilbert.Polynomial.GradedHilbert.grading R n →+*ᵍ Hilbert.Polynomial.GradedHilbert.grading S n where
  __ := MvPolynomial.map φ
  map_mem hf := hf.map φ

def extendedHomogeneousIdeal (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading S n) := I.map (gradedCoefficientMap (algebraMap R S))

theorem polynomialTensor_ideal_map (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    (extendedHomogeneousIdeal (S := S) I).toIdeal =
      (I.toIdeal.map (Algebra.TensorProduct.includeRight (A := S) (R := R))).map
        (MvPolynomial.algebraTensorAlgEquiv R S).toRingHom := by
  erw [Ideal.map_map]
  have h : (MvPolynomial.algebraTensorAlgEquiv (σ := Fin (n + 1)) R S).toRingHom.comp
      (Algebra.TensorProduct.includeRight (A := S) (R := R)).toRingHom =
        MvPolynomial.map (algebraMap R S) := by
    apply RingHom.ext
    intro f
    change MvPolynomial.algebraTensorAlgEquiv R S (1 ⊗ₜ[R] f) = _
    simpa only [one_smul] using MvPolynomial.algebraTensorAlgEquiv_tmul R S 1 f
  erw [h]
  rfl

def quotientBaseChangeEquiv (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    S ⊗[R] (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) ≃ₐ[S]
      Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ (extendedHomogeneousIdeal (S := S) I).toIdeal :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) S I.toIdeal).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S) (polynomialTensor_ideal_map I))

theorem quotientBaseChangeEquiv_tmul (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (s : S) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    quotientBaseChangeEquiv I (s ⊗ₜ[R] Ideal.Quotient.mk I.toIdeal f) =
      Ideal.Quotient.mk (extendedHomogeneousIdeal (S := S) I).toIdeal
        (s • MvPolynomial.map (algebraMap R S) f) := by
  change Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv R S)
    (polynomialTensor_ideal_map I)
      ((Algebra.TensorProduct.tensorQuotientEquiv (R := R) S (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) S I.toIdeal)
        (s ⊗ₜ[R] Ideal.Quotient.mk I.toIdeal f)) = _
  erw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul, Ideal.quotientEquivAlg_mk,
    MvPolynomial.algebraTensorAlgEquiv_tmul]

theorem quotientGrading_baseChange_map (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    ((Graded.Quotient.GradedHilbert.quotientGrading I d).baseChange S).map (quotientBaseChangeEquiv (S := S) I).toLinearMap =
      Graded.Quotient.GradedHilbert.quotientGrading (extendedHomogeneousIdeal (S := S) I) d := by
  classical
  let J := extendedHomogeneousIdeal (S := S) I
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro z ⟨y, hy, rfl⟩
    obtain ⟨f, hf, rfl⟩ := hy
    change quotientBaseChangeEquiv I (1 ⊗ₜ[R] Ideal.Quotient.mk I.toIdeal f) ∈ Graded.Quotient.GradedHilbert.quotientGrading J d
    rw [quotientBaseChangeEquiv_tmul, one_smul]
    exact ⟨MvPolynomial.map (algebraMap R S) f, hf.map (algebraMap R S), rfl⟩
  · rintro z ⟨f, hf, rfl⟩
    rw [← f.support_sum_monomial_coeff, map_sum]
    apply Submodule.sum_mem
    intro a ha
    have had : a.degree = d := (Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support f d).mp hf a ha
    have hmon : Ideal.Quotient.mk I.toIdeal (monomial a 1) ∈ Graded.Quotient.GradedHilbert.quotientGrading I d :=
      ⟨monomial a 1, isHomogeneous_monomial _ had, rfl⟩
    refine ⟨f.coeff a ⊗ₜ[R] Ideal.Quotient.mk I.toIdeal (monomial a 1),
      Submodule.tmul_mem_baseChange_of_mem _ hmon, ?_⟩
    rw [AlgEquiv.toLinearMap_apply, quotientBaseChangeEquiv_tmul]
    simp only [MvPolynomial.map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]
    rfl

def quotientGradingBaseChangeEquiv (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    S ⊗[R] Graded.Quotient.GradedHilbert.quotientGrading I d ≃ₗ[S] Graded.Quotient.GradedHilbert.quotientGrading (extendedHomogeneousIdeal (S := S) I) d :=
  (LinearEquiv.ofBijective ((Graded.Quotient.GradedHilbert.quotientGrading I d).toBaseChange S)
    (DirectSum.toBaseChange_bijective (Graded.Quotient.GradedHilbert.quotientGrading I) d)).trans
    ((quotientBaseChangeEquiv I).toLinearEquiv.ofSubmodules _ _ (quotientGrading_baseChange_map I d))

/-- Homogeneous degree quotients commute with arbitrary coefficient-ring
extension. This is a module isomorphism, not only a dimension equality. -/
def degreeQuotientBaseChangeEquiv (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    S ⊗[R] Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d ≃ₗ[S]
      Hilbert.Polynomial.GradedHilbert.DegreeQuotient (extendedHomogeneousIdeal (S := S) I).toIdeal d :=
  ((Graded.Quotient.GradedHilbert.degreeQuotientEquivQuotientGrading I d).baseChange R S).trans
    ((quotientGradingBaseChangeEquiv I d).trans
      (Graded.Quotient.GradedHilbert.degreeQuotientEquivQuotientGrading (extendedHomogeneousIdeal (S := S) I) d).symm)

theorem degreeQuotientBaseChangeEquiv_tmul (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ)
    (s : S) (f : Hilbert.Polynomial.GradedHilbert.grading R n d) :
    degreeQuotientBaseChangeEquiv I d (s ⊗ₜ[R] (Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ f) =
      (Hilbert.Polynomial.GradedHilbert.degreeRelations (extendedHomogeneousIdeal (S := S) I).toIdeal d).mkQ
        ⟨s • MvPolynomial.map (algebraMap R S) f.val,
          (Hilbert.Polynomial.GradedHilbert.grading S n d).smul_mem s (f.property.map (algebraMap R S))⟩ := by
  apply (Graded.Quotient.GradedHilbert.degreeQuotientEquivQuotientGrading (extendedHomogeneousIdeal (S := S) I) d).injective
  simp only [degreeQuotientBaseChangeEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.baseChange_tmul,
    Graded.Quotient.GradedHilbert.degreeQuotientEquivQuotientGrading_mk]
  apply Subtype.ext
  change quotientBaseChangeEquiv I (s ⊗ₜ[R] Ideal.Quotient.mk I.toIdeal f.val) =
    Ideal.Quotient.mk (extendedHomogeneousIdeal (S := S) I).toIdeal
      (s • MvPolynomial.map (algebraMap R S) f.val)
  exact quotientBaseChangeEquiv_tmul I s f.val

theorem coordinateQuotient_flat_iff (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Module.Flat R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) ↔
      ∀ d : ℕ, Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := by
  rw [Module.Flat.equiv_iff (DirectSum.decomposeLinearEquiv (Graded.Quotient.GradedHilbert.quotientGrading I)),
    Module.Flat.directSum_iff]
  exact forall_congr' fun d =>
    (Module.Flat.equiv_iff (Graded.Quotient.GradedHilbert.degreeQuotientEquivQuotientGrading I d)).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert
