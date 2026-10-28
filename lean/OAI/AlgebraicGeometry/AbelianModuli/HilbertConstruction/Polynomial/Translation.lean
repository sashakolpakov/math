import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.VariableSequence
import Mathlib.Algebra.Algebra.Equiv

/-! # Translation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.Translation

noncomputable section

/-! Translation carries the regular sequence of polynomial variables to the coordinate differences at an arbitrary rational point. -/
universe u v
variable {R : Type u} [CommRing R] {ι : Type v}

def polynomialTranslation (a : ι → R) : MvPolynomial ι R ≃ₐ[R] MvPolynomial ι R :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i => MvPolynomial.X i - MvPolynomial.C (a i))
    (MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C (a i))
    (by ext i; simp)
    (by ext i; simp)

@[simp] theorem polynomialTranslation_X (a : ι → R) (i : ι) :
    polynomialTranslation a (MvPolynomial.X i) =
      MvPolynomial.X i - MvPolynomial.C (a i) :=
  MvPolynomial.aeval_X _ _

theorem coordinate_difference_list_regular [Nontrivial R]
    (a : ι → R) (xs : List ι) (hxs : xs.Nodup) :
    Regular.SequenceBasic.RingTheory.Sequence.IsRegular (MvPolynomial ι R)
      (xs.map fun i => MvPolynomial.X i - MvPolynomial.C (a i)) := by
  have hcongr : Regular.SequenceBasic.RingTheory.Sequence.IsRegular (MvPolynomial ι R) (xs.map (MvPolynomial.X : ι → MvPolynomial ι R)) ↔
      Regular.SequenceBasic.RingTheory.Sequence.IsRegular (MvPolynomial ι R)
        (xs.map fun i => MvPolynomial.X i - MvPolynomial.C (a i)) := by
    apply Regular.SequenceBasic.AddEquiv.isRegular_congr
      (e := (polynomialTranslation a).toRingEquiv.toAddEquiv)
    apply List.forall₂_map_left_iff.mpr
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro i _ p
    change polynomialTranslation a (MvPolynomial.X i * p) =
      (MvPolynomial.X i - MvPolynomial.C (a i)) * polynomialTranslation a p
    rw [map_mul, polynomialTranslation_X]
  exact hcongr.mp (VariableSequence.variable_list_regular xs hxs)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.Translation
