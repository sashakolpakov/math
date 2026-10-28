import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart

/-! # Homogeneous Coordinate Map -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousCoordinateMap

noncomputable section

/-! A tuple of actual homogeneous linear forms induces the graded
coordinate homomorphism used by the projective projection construction. -/

def ofForms {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n)
    (hL : ∀ i, L i ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n where
  __ := (MvPolynomial.aeval L).toRingHom
  map_mem {d} {p} hp := by
    change MvPolynomial.IsHomogeneous (MvPolynomial.aeval L p) d
    rw [MvPolynomial.aeval_def]
    simpa only [one_mul, MvPolynomial.algebraMap_eq] using MvPolynomial.IsHomogeneous.eval₂ hp
      (MvPolynomial.C : ℂ →+* Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n) L (MvPolynomial.isHomogeneous_C _) hL

theorem ofForms_X {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n)
    (hL : ∀ i, L i ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (i : Fin (m + 1)) :
    ofForms L hL (MvPolynomial.X i) = L i := MvPolynomial.aeval_X _ _

theorem ofForms_C {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n)
    (hL : ∀ i, L i ∈ Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (z : ℂ) :
    ofForms L hL (MvPolynomial.C z) = MvPolynomial.C z := MvPolynomial.aeval_C _ _

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousCoordinateMap
