import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FlatEquationModel

/-! # Finite Equation Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FiniteEquationCoordinates.GradedHilbert

noncomputable section

/-! Finite native equations compute the exact saturated coordinates
after every coefficient change, without assumptions on the test ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {A T : Type u} [CommRing A] [CommRing T] {n : ℕ}
variable {a : Spec (.of A) ⟶ S}
variable {F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)}
variable (E : AffineEquationModel.GradedHilbert.NativeAffineEquations a F)

theorem nativeFiniteEquations_coordinates :
    Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a F = Projective.Saturation.GradedHilbert.projectiveSaturation
      (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal E.generators E.degree E.homogeneous) := by
  simpa only [AffineEquationModel.GradedHilbert.nativeEquationExtendedIdeal_eq] using
    FlatEquationModel.GradedHilbert.nativeEquationModel_saturated_coordinates (B := A) E

theorem nativeFiniteEquations_baseChange_coordinates (φ : A →+* T) :
    Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (Spec.map (CommRingCat.ofHom φ) ≫ a)
      (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ) F) =
      Projective.Saturation.GradedHilbert.projectiveSaturation
        ((Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal E.generators E.degree E.homogeneous).map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)) := by
  rw [Affine.HomogeneousCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_baseChange, nativeFiniteEquations_coordinates E]
  exact Projective.SaturationBaseChangeEquality.GradedHilbert.projectiveSaturation_map_eq_of_eq φ
    (Projective.Saturation.GradedHilbert.projectiveSaturation (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal E.generators E.degree E.homogeneous))
    (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal E.generators E.degree E.homogeneous)
    (Projective.Saturation.GradedHilbert.projectiveSaturation_idempotent _)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FiniteEquationCoordinates.GradedHilbert
