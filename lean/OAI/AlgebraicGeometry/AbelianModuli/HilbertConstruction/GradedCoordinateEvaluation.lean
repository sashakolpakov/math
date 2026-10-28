import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.Fractions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedLinearCoordinateIsomorphism

/-! # Graded Coordinate Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedCoordinateEvaluation

noncomputable section

/-! Polynomial evaluation after a coefficient-preserving graded map is
evaluation at its transformed homogeneous coordinates. -/
universe u
variable {R B : Type u} [CommRing R] [CommRing B] {n : ℕ}
variable (g : Projective.ProjectivePresentations.coordinateGrading R n →+*ᵍ Projective.ProjectivePresentations.coordinateGrading R n)
variable (hg : ∀ r : R, g (MvPolynomial.C r) = MvPolynomial.C r)
variable (c : R →+* B) (v : Fin (n + 1) → B)

def gradedCoordinateValues : Fin (n + 1) → B :=
  fun i => MvPolynomial.eval₂Hom c v (g (MvPolynomial.X i))

include hg in
theorem gradedCoordinateEvaluation_comp :
    (MvPolynomial.eval₂Hom c v).comp g.toRingHom =
      MvPolynomial.eval₂Hom c (gradedCoordinateValues g c v) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    change MvPolynomial.eval₂Hom c v (g (MvPolynomial.C r)) = _
    rw [hg, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_C]
  · intro i
    exact (MvPolynomial.eval₂Hom_X' c (gradedCoordinateValues g c v) i).symm

include hg in
theorem gradedCoordinateEvaluation_apply (p : Projective.ProjectivePresentations.coordinateRing R n) :
    MvPolynomial.eval₂Hom c v (g p) =
      MvPolynomial.eval₂Hom c (gradedCoordinateValues g c v) p :=
  RingHom.congr_fun (gradedCoordinateEvaluation_comp g hg c v) p

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedCoordinateEvaluation
