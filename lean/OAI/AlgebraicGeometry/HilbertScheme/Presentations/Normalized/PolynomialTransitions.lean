import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialKernel
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneratedIdealReconstruction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.GeneratorsBaseChange

/-! # Polynomial Transitions -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialTransitions.GradedHilbert

noncomputable section

/-! Polynomial ideals on normalized Grassmannian charts agree on their
actual overlaps and commute with arbitrary coefficient extension. -/

open _root_.MvPolynomial

universe u
variable {R : Type u} [CommRing R] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem normalizedPolynomialIdeal_eq_of_kernel_eq (a b : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N)
    (Q K : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R) (hQ : Matrices.Grassmannian.IsNormalized a Q) (hK : Matrices.Grassmannian.IsNormalized b K)
    (h : (Matrix.toLin' Q).ker = (Matrix.toLin' K).ker) :
    PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q = PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal b K := by
  apply GeneratedIdealReconstruction.GradedHilbert.homogeneousGeneratorsIdeal_eq_of_degreeRelations_eq
  change Hilbert.Polynomial.GradedHilbert.degreeRelations (PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal N =
    Hilbert.Polynomial.GradedHilbert.degreeRelations (PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal b K).toIdeal N
  rw [PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal_degreeRelations a Q hQ,
    PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal_degreeRelations b K hK, h]

theorem normalizedPolynomialIdeal_transition (a b : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N)
    (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R) (hQ : Matrices.Grassmannian.IsNormalized a Q)
    (hb : IsUnit (Matrices.Grassmannian.selectedColumns b Q).det) :
    PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q = PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal b (Matrices.Grassmannian.normalizeColumns b Q) := by
  apply normalizedPolynomialIdeal_eq_of_kernel_eq a b Q _ hQ
    (Matrices.Grassmannian.normalizeColumns_normalized b Q hb)
  exact (OverlapEquations.Grassmannian.quotientCompatibility_iff_kernel_eq a b Q _ hQ
    (Matrices.Grassmannian.normalizeColumns_normalized b Q hb)).mp
      ((OverlapEquations.Grassmannian.quotientCompatibility_iff_transition a b Q _ hQ).mpr ⟨hb, rfl⟩)

omit [DecidableEq ι] in
theorem normalizedPolynomialIdeal_baseChange {S : Type u} [CommRing S] [Algebra R S]
    (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R) :
    Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) (PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q) =
      PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Q.map (algebraMap R S)) := by
  apply HomogeneousIdeal.ext
  change Ideal.map (MvPolynomial.map (algebraMap R S))
      (Ideal.span (Set.range (PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator a Q))) =
    Ideal.span (Set.range (PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator a (Q.map (algebraMap R S))))
  rw [Ideal.map_span, ← Set.range_comp]
  congr 2
  funext j
  exact PolynomialGenerators.GradedHilbert.normalizedPolynomialGenerator_map (algebraMap R S) a Q j

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialTransitions.GradedHilbert
