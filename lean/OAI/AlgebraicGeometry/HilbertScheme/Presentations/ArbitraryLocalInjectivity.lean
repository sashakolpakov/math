import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.ParameterKernel

/-! # Arbitrary Local Injectivity -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryLocalInjectivity.GradedHilbert

noncomputable section

/-! The actual bounded Hilbert family distinguishes parameters over
every local ring, including nonnoetherian local rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {n N : ℕ}
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem boundedHilbertUniversalFamily_arbitrary_local_injective
    (P : Polynomial ℚ)
    (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) P)
    (hN : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat)
    (f : Spec (.of R) ⟶ S) :
    Function.Injective (fun x : Over.mk f ⟶ BoundedHilbert.Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S
        (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) =>
      Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P))) := by
  intro x y h
  obtain ⟨Q, hQ, hx⟩ := Local.ParameterKernel.GradedHilbert.exists_local_hilbert_parameter_coordinate_kernel P hP hN hr f x
  obtain ⟨D, hD, hy⟩ := Local.ParameterKernel.GradedHilbert.exists_local_hilbert_parameter_coordinate_kernel P hP hN hr f y
  have he : Q = D := by
    apply Module.Grassmannian.ext
    rw [hQ, hD]
    exact congrArg (fun F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f) =>
      DegreeCoordinateRelations.GradedHilbert.degreeCoordinateRelations (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) N) h
  apply (cancel_mono (BoundedHilbert.Data.GradedHilbert.boundedHilbertParameterOver (ι := ι) n N S
    (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P))).mp
  exact hx.symm.trans ((congrArg (Relative.AffineQuotientPoint.Grassmannian.relativeQuotientClassifyingPoint f) he).trans hy)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ArbitraryLocalInjectivity.GradedHilbert
