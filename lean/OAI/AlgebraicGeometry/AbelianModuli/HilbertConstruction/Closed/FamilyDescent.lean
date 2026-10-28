import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DensePolynomialDescent
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.ClosedFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ClosedFamily.CoordinateBaseChange

/-! # Family Descent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed

noncomputable section

/-! Injective coefficient recovery preserves the prescribed Hilbert polynomial of a noetherian flat closed model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem Families.FlatClosedFamily.hilbert_of_injective_coefficient_recovery
    {C A : CommRingCat.{u}} [IsNoetherianRing C] (φ : C ⟶ A)
    (hinj : Function.Injective φ.hom) {n : ℕ} {P : Polynomial ℚ}
    (G : Families.FlatClosedFamily (Projective.ProjectivePresentations.affineProjectiveSpace C n)) (F : HilbertConstruction.Flat.ClosedFamilies.FlatClosedHilbertFamily A n P)
    (hF : F.val = G.pullbackAlong (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) (Spec.map φ)
      (Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback φ n)) :
    ∀ p : PrimeSpectrum C, HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) G.homogeneousIdeal)).toIdeal P := by
  let : Algebra C A := φ.hom.toAlgebra
  have : Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading G.homogeneousIdeal)) := G.homogeneousIdeal_flat
  have he : F.val.homogeneousIdeal = HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) G.homogeneousIdeal) :=
    (congrArg Families.FlatClosedFamily.homogeneousIdeal hF).trans (G.homogeneousIdeal_coefficientBaseChange φ)
  apply DensePolynomialDescent.noetherianFlat_hilbertPolynomial_dense_descent hinj G.homogeneousIdeal P
  intro q
  have hp := F.property q
  rw [he, Projective.SaturationBaseChange.projectiveSaturation_baseChange] at hp
  exact hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Closed
