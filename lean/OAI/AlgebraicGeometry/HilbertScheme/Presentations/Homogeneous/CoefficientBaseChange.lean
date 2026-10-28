import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange

/-! # Coefficient Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CoefficientBaseChange.GradedHilbert

noncomputable section

/-! Actual homogeneous polynomial pieces commute with arbitrary coefficient base change. -/

open _root_.MvPolynomial TensorProduct

universe u v

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] {n : ℕ}

theorem homogeneousPiece_baseChange_map (d : ℕ) :
    ((Hilbert.Polynomial.GradedHilbert.grading R n d).baseChange S).map (MvPolynomial.algebraTensorAlgEquiv R S).toLinearMap =
      Hilbert.Polynomial.GradedHilbert.grading S n d := by
  classical
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro z ⟨p, hp, rfl⟩
    change MvPolynomial.algebraTensorAlgEquiv R S (1 ⊗ₜ[R] p) ∈ Hilbert.Polynomial.GradedHilbert.grading S n d
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
    exact hp.map (algebraMap R S)
  · intro p hp
    rw [← p.support_sum_monomial_coeff]
    apply Submodule.sum_mem
    intro a ha
    have had : a.degree = d := (Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support p d).mp hp a ha
    refine ⟨p.coeff a ⊗ₜ[R] monomial a (1 : R),
      Submodule.tmul_mem_baseChange_of_mem _ (isHomogeneous_monomial (1 : R) had), ?_⟩
    rw [AlgEquiv.toLinearMap_apply, MvPolynomial.algebraTensorAlgEquiv_tmul]
    simp only [MvPolynomial.map_monomial, map_one, smul_monomial, smul_eq_mul, mul_one]

def homogeneousPieceBaseChangeEquiv (d : ℕ) : S ⊗[R] Hilbert.Polynomial.GradedHilbert.grading R n d ≃ₗ[S] Hilbert.Polynomial.GradedHilbert.grading S n d :=
  (LinearEquiv.ofBijective ((Hilbert.Polynomial.GradedHilbert.grading R n d).toBaseChange S)
    (DirectSum.toBaseChange_bijective (Hilbert.Polynomial.GradedHilbert.grading R n) d)).trans
    ((MvPolynomial.algebraTensorAlgEquiv R S).toLinearEquiv.ofSubmodules _ _ (homogeneousPiece_baseChange_map d))

theorem homogeneousPieceBaseChangeEquiv_tmul (d : ℕ) (s : S) (f : Hilbert.Polynomial.GradedHilbert.grading R n d) :
    (homogeneousPieceBaseChangeEquiv (S := S) d (s ⊗ₜ[R] f)).val =
      s • MvPolynomial.map (algebraMap R S) f.val :=
  MvPolynomial.algebraTensorAlgEquiv_tmul R S s f.val

theorem homogeneousPieceBaseChangeEquiv_quotient (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ)
    (x : S ⊗[R] Hilbert.Polynomial.GradedHilbert.grading R n d) :
    Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := S) I d (((Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ.lTensor S) x) =
      (Hilbert.Polynomial.GradedHilbert.degreeRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d).mkQ
        (homogeneousPieceBaseChangeEquiv (S := S) d x) := by
  induction x using TensorProduct.inductionOn with
  | tmul s f =>
    rw [LinearMap.lTensor_tmul, Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv_tmul]
    apply congrArg (Hilbert.Polynomial.GradedHilbert.degreeRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d).mkQ
    apply Subtype.ext
    exact (homogeneousPieceBaseChangeEquiv_tmul d s f).symm
  | add x y hx hy => simp only [LinearEquiv.map_add, LinearMap.map_add, hx, hy]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.CoefficientBaseChange.GradedHilbert
