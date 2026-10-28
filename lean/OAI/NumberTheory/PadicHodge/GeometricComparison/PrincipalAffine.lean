import OAI.NumberTheory.PadicHodge.GeometricComparison.RelativeSectionCoefficients
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Principal Affine -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalAffine.PrincipalAffineChart

noncomputable section

/-! Principal localization gives an actual open affine chart between the native relative models, with its exact image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

def map : RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R B ⟶ RelativeSectionCoefficients.AffineCoordinates.relativeSpecModel R A :=
  RelativeSectionCoefficients.RelativeSpecMaps.map (IsScalarTower.toAlgHom R A B)

theorem isOpenImmersion (a : A) [IsLocalization.Away a B] : IsOpenImmersion (map R A B).left :=
  IsOpenImmersion.of_isLocalization a

theorem image_top (a : A) [IsLocalization.Away a B] :
    letI : IsOpenImmersion (map R A B).left := isOpenImmersion R A B a
    (map R A B).left ''ᵁ ⊤ = (PrimeSpectrum.basicOpen a : (Spec (CommRingCat.of A)).Opens) := by
  let : IsOpenImmersion (map R A B).left := isOpenImmersion R A B a
  apply (Scheme.Hom.image_top_eq_opensRange (map R A B).left).trans
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range B a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalAffine.PrincipalAffineChart
