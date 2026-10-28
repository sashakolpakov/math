import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialTransitions

/-! # Polynomial Kernel Recovery -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialKernelRecovery.GradedHilbert

noncomputable section

/-! The actual normalized polynomial ideal recovers its matrix kernel,
including comparisons between different normalized charts. -/

universe u
variable {R : Type u} [CommRing R] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem normalizedPolynomialIdeal_eq_iff_kernel_eq
    (a b : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (Q L : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R)
    (hQ : Matrices.Grassmannian.IsNormalized a Q) (hL : Matrices.Grassmannian.IsNormalized b L) :
    PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q = PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal b L ↔
      (Matrix.toLin' Q).ker = (Matrix.toLin' L).ker := by
  constructor
  · intro h
    have hd := congrArg (fun J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) => Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal N) h
    rw [PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal_degreeRelations a Q hQ,
      PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal_degreeRelations b L hL] at hd
    exact Submodule.map_injective_of_injective (Homogeneous.CoordinateBasis.GradedHilbert.coordinateDegreeBasis R n N).equivFun.symm.injective hd
  · exact PolynomialTransitions.GradedHilbert.normalizedPolynomialIdeal_eq_of_kernel_eq a b Q L hQ hL

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialKernelRecovery.GradedHilbert
