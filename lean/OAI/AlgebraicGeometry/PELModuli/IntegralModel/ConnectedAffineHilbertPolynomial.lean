import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatHilbertPolynomialPartition
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CanonicalFiberPolynomial

/-! # Connected Affine Hilbert Polynomial -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConnectedAffineHilbertPolynomial

noncomputable section

/-! A flat projective Hilbert family over a connected noetherian
affine test has one actual Hilbert polynomial on every field fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatHilbertPolynomialPartition.PolarizationEmbedding

theorem exists_connected_affine_fiber_polynomial
    {R : Type} [CommRing R] [IsNoetherianRing R]
    [PreconnectedSpace (PrimeSpectrum R)] [Nonempty (PrimeSpectrum R)]
    {S : Scheme.{0}} {n : ℕ} (f : Spec (.of R) ⟶ S)
    (F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) :
    ∃ P : Polynomial ℚ, HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P := by
  let I := HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F
  have : Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)) := HilbertScheme.Presentations.Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat n f F
  let p₀ : PrimeSpectrum R := Classical.choice inferInstance
  let P := FlatHilbertPolynomialPartition.PolarizationEmbedding.residueHilbertPolynomial I p₀
  refine ⟨P, HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert.canonicalFiberHilbertPolynomial_of_noetherian_affine_residues f F P ?_⟩
  intro p
  have h : FlatHilbertPolynomialPartition.PolarizationEmbedding.residueHilbertPolynomial I p = P :=
    (FlatHilbertPolynomialPartition.PolarizationEmbedding.residueHilbertPolynomial_isLocallyConstant I).apply_eq_of_preconnectedSpace p p₀
  apply (HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff
    (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I) P).mpr
  rw [← h]
  exact FlatHilbertPolynomialPartition.PolarizationEmbedding.residueHilbertPolynomial_spec I p

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConnectedAffineHilbertPolynomial
