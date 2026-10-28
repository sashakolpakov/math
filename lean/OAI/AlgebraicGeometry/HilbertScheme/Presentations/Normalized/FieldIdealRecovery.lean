import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SingleDegreeIdealReconstruction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Truncation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial

/-! # Field Ideal Recovery -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.FieldIdealRecovery.GradedHilbert

noncomputable section

/-! A normalized degree-N field ideal with the prescribed quotient rank is
recovered exactly from the canonical saturated ideal when N is large enough. -/

universe u
variable {K : Type u} [Field K] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem normalizedFieldIdeal_eq_degreeGenerated_saturation
    (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) K) (hQ : Matrices.Grassmannian.IsNormalized a Q)
    (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q).toIdeal P)
    (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat) :
    PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q = DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal (Projective.Saturation.GradedHilbert.projectiveSaturation (PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q)) N := by
  let J := PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a Q
  have hPJ : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.Saturation.GradedHilbert.projectiveSaturation J).toIdeal P :=
    (Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff J P).mpr hP
  have hs := (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n P K (Projective.Saturation.GradedHilbert.projectiveSaturation J)
    (Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated J) hPJ).2 N hN
  have hdim : Hilbert.Polynomial.GradedHilbert.hilbertFunction J.toIdeal N = Hilbert.Polynomial.GradedHilbert.hilbertFunction (Projective.Saturation.GradedHilbert.projectiveSaturation J).toIdeal N := by
    have hq : Hilbert.Polynomial.GradedHilbert.hilbertFunction J.toIdeal N = Fintype.card ι :=
      (PolynomialKernel.GradedHilbert.normalizedPolynomialDegreeQuotientEquiv a Q hQ).finrank_eq.trans (Module.finrank_fintype_fun_eq_card K)
    rw [hq, hr, ← hs]
    simp only [Rat.num_natCast, Int.toNat_natCast]
  exact SingleDegreeIdealReconstruction.GradedHilbert.normalizedPolynomialIdeal_eq_degreeGenerated (Projective.Saturation.GradedHilbert.projectiveSaturation J) N a Q
    (Hilbert.Polynomial.GradedHilbert.degreeRelations_eq_of_le_of_hilbertFunction_eq (Projective.Saturation.GradedHilbert.le_projectiveSaturation J) N hdim)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.FieldIdealRecovery.GradedHilbert
