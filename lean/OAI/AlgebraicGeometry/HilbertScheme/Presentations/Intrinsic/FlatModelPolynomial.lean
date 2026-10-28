import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FlatEquationModel
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FlatPolynomialDescent
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CanonicalFiberPolynomial

/-! # Flat Model Polynomial -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FlatModelPolynomial.GradedHilbert

noncomputable section

/-! The actual native family polynomial is inherited by the constructed
Noetherian local flat equation model, hence by every fiber of that model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {A B : Type u} [CommRing A] [IsLocalRing A]
variable [CommRing B] [IsNoetherianRing B] [Algebra B A] {n : ℕ}
variable {a : Spec (.of A) ⟶ S}
variable {F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)}
variable (E : AffineEquationModel.GradedHilbert.NativeAffineEquations a F)

theorem nativeLocalFlatEquationModel_hilbertPolynomial
    (P : Polynomial ℚ) (hP : CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial F P) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal
      (S := (FlatEquationModel.GradedHilbert.nativeLocalFlatEquationModel (B := B) E).R) (AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B)).toIdeal P := by
  let M := FlatEquationModel.GradedHilbert.nativeLocalFlatEquationModel (B := B) E
  let I := Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := M.R) (AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B)
  have : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := M.flat
  let p : PrimeSpectrum A := IsLocalRing.closedPoint A
  let K := p.asIdeal.ResidueField
  let : Algebra M.R K := ((algebraMap A K).comp (algebraMap M.R A)).toAlgebra
  let : IsScalarTower M.R A K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Local.FlatPolynomialDescent.GradedHilbert.localFlat_hilbertPolynomial_of_saturated_baseChange (K := K) I
    (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a F) (FlatEquationModel.GradedHilbert.nativeLocalFlatEquationModel_coordinates (B := B) E)
    P (hP.affine_residue p)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FlatModelPolynomial.GradedHilbert
