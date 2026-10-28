import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.SaturationBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.HomogeneousCoordinateBaseChange

/-! # Flat Coefficient Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FlatCoefficientCoordinates.GradedHilbert

noncomputable section

/-! Canonical homogeneous coordinates of native families commute exactly
with every flat coefficient extension, in all degrees and over arbitrary rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
variable {S : Scheme.{u}} {n : ℕ}

theorem affineNativeHomogeneousIdeal_flat_baseChange (f : Spec (.of R) ⟶ S)
    (F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) :
    Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ f)
      (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f (algebraMap R A)) F) =
        Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F) := by
  rw [Affine.HomogeneousCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_baseChange]
  exact Presentations.Flat.SaturationBaseChange.GradedHilbert.flat_extendedHomogeneousIdeal_saturation _ (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n f F)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.FlatCoefficientCoordinates.GradedHilbert
