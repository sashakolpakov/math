import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ModelCartesianRecovery
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.HomogeneousFamilyConstruction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SaturationBaseChangeEquality

/-! # Flat Equation Model -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FlatEquationModel.GradedHilbert

noncomputable section

/-! Retain the homogeneous ideal of the local flat coefficient model,
including its exact saturated coordinates on the original native family. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {A B : Type u} [CommRing A] [IsLocalRing A]
variable [CommRing B] [IsNoetherianRing B] [Algebra B A] {n : ℕ}
variable {a : Spec (.of A) ⟶ S}
variable {F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)}
variable (E : AffineEquationModel.GradedHilbert.NativeAffineEquations a F)

def nativeLocalFlatEquationModel :
    Noetherian.ProjectiveFlatFactorization.GradedHilbert.NoetherianLocalFlatCoefficientModel (A := A) (AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B) := by
  have : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading
      (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) (AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B)))) :=
    Presentations.Flat.ModelCartesianRecovery.GradedHilbert.nativeEquationExtendedIdeal_flat (B := B) a F E
  exact Classical.choice (Noetherian.ProjectiveFlatFactorization.GradedHilbert.exists_noetherian_local_flat_coefficient_model (A := A)
    (AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B))

omit [IsLocalRing A] [IsNoetherianRing B] in
theorem nativeEquationModel_saturated_coordinates :
    Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a F = Projective.Saturation.GradedHilbert.projectiveSaturation (AffineEquationModel.GradedHilbert.nativeEquationExtendedIdeal E B) := by
  change ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf (F.val.comap (Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n a).hom) = _
  rw [← AffineEquationModel.GradedHilbert.nativeEquationModel_realization E B, Global.PolynomialInclusion.closedImmersion_comp_iso_ker,
    ← Scheme.IdealSheafData.comap_comp, Iso.hom_inv_id, Scheme.IdealSheafData.comap_id]
  rfl

theorem nativeLocalFlatEquationModel_coordinates :
    Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a F = Projective.Saturation.GradedHilbert.projectiveSaturation
      (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A)
        (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := (nativeLocalFlatEquationModel (B := B) E).R)
          (AffineEquationModel.GradedHilbert.nativeEquationModelIdeal E B))) := by
  rw [Homogeneous.IdealTower.GradedHilbert.extendedHomogeneousIdeal_tower]
  exact nativeEquationModel_saturated_coordinates (B := B) E

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FlatEquationModel.GradedHilbert
