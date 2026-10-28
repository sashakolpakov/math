import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange

/-! # Ideal Tower -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.IdealTower.GradedHilbert

noncomputable section

/-! Homogeneous coefficient extension agrees along an algebra tower. -/

universe u v w
variable {B : Type u} [CommRing B] {C : Type v} [CommRing C] {A : Type w} [CommRing A]
variable [Algebra B C] [Algebra C A] [Algebra B A] [IsScalarTower B C A] {n : ℕ}

theorem extendedHomogeneousIdeal_tower (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading B n)) :
    Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := C) I) =
      Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I := by
  apply HomogeneousIdeal.ext
  change (I.toIdeal.map (MvPolynomial.map (algebraMap B C))).map
    (MvPolynomial.map (algebraMap C A)) = I.toIdeal.map (MvPolynomial.map (algebraMap B A))
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  exact (MvPolynomial.map_map (algebraMap B C) (algebraMap C A) p).trans
    (congrArg (fun f : B →+* A => MvPolynomial.map f p) (IsScalarTower.algebraMap_eq B C A).symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.IdealTower.GradedHilbert
