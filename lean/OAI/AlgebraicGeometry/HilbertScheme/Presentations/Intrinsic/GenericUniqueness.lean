import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedFlatGenericUniqueness
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.HomogeneousFamilyConstruction

/-! # Generic Uniqueness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.GenericUniqueness.GradedHilbert

noncomputable section

/-! A native flat projective closed family over an integral affine test
is uniquely determined by its actual generic fiber. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {R K : Type u} [CommRing R] [IsDomain R]
variable [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}

theorem nativeFamily_generic_pullback_injective (a : Spec (CommRingCat.of R) ⟶ S) :
    Function.Injective (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
      (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a (algebraMap R K))) := by
  intro F G h
  apply HomogeneousFamilyConstruction.GradedHilbert.affineNativeHomogeneousIdeal_injective n a
  let I := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a F
  let J := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a G
  let : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat n a F
  let : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J)) := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat n a G
  apply SaturatedFlatGenericUniqueness.GradedHilbert.saturatedFlat_eq_of_generic_saturation (K := K) I J
    (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n a F) (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n a G)
  have he := congrArg (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ a)) h
  rw [Affine.HomogeneousCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_baseChange, Affine.HomogeneousCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_baseChange] at he
  exact he

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.GenericUniqueness.GradedHilbert
