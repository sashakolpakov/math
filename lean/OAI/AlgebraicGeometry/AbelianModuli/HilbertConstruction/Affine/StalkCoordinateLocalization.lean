import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RationalPointIdeal
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Stalk Coordinate Localization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StalkCoordinateLocalization

noncomputable section

/-! The actual stalk of an affine scheme is its coordinate-ring localization at the corresponding point. Its structure morphism is exactly the affine coordinate map of the germ homomorphism. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable (T : Scheme.{u}) [IsAffine T] (x : T)

local instance : (T.isoSpec.hom x).asIdeal.IsPrime :=
  (show PrimeSpectrum Γ(T, ⊤) from T.isoSpec.hom x).isPrime

theorem affineTopPrimeIdeal_eq_isoSpec :
    (isAffineOpen_top T).primeIdealOf ⟨x, trivial⟩ = T.isoSpec.hom x := by
  have hp : T.isoSpec.inv ((isAffineOpen_top T).primeIdealOf ⟨x, trivial⟩) = x := by
    simpa only [IsAffineOpen.fromSpec_top] using
      (isAffineOpen_top T).fromSpec_primeIdealOf ⟨x, trivial⟩
  have h := congrArg T.isoSpec.hom hp
  change (T.isoSpec.inv ≫ T.isoSpec.hom)
    ((isAffineOpen_top T).primeIdealOf ⟨x, trivial⟩) = T.isoSpec.hom x at h
  rw [T.isoSpec.inv_hom_id] at h
  exact h

@[instance_reducible]
def affineStalkCoordinateAlgebra : Algebra Γ(T, ⊤) (T.presheaf.stalk x) :=
  (T.presheaf.germ ⊤ x trivial).hom.toAlgebra

theorem affineStalkCoordinate_isLocalization :
    let : Algebra Γ(T, ⊤) (T.presheaf.stalk x) := affineStalkCoordinateAlgebra T x;
    IsLocalization (T.isoSpec.hom x).asIdeal.primeCompl (T.presheaf.stalk x) := by
  let : Algebra Γ(T, ⊤) (T.presheaf.stalk x) := affineStalkCoordinateAlgebra T x
  have h := (isAffineOpen_top T).isLocalization_stalk ⟨x, trivial⟩
  rwa [affineTopPrimeIdeal_eq_isoSpec T x] at h

def affineStalkCoordinateLocalizationEquiv :
    let : Algebra Γ(T, ⊤) (T.presheaf.stalk x) := affineStalkCoordinateAlgebra T x;
    Localization.AtPrime (T.isoSpec.hom x).asIdeal ≃ₐ[Γ(T, ⊤)] T.presheaf.stalk x := by
  letI : Algebra Γ(T, ⊤) (T.presheaf.stalk x) := affineStalkCoordinateAlgebra T x
  letI : IsLocalization (T.isoSpec.hom x).asIdeal.primeCompl (T.presheaf.stalk x) :=
    affineStalkCoordinate_isLocalization T x
  exact IsLocalization.algEquiv (T.isoSpec.hom x).asIdeal.primeCompl
    (Localization.AtPrime (T.isoSpec.hom x).asIdeal) (T.presheaf.stalk x)

theorem affineCoordinateMap_germ_eq_fromSpecStalk :
    QuotientCoefficientMap.affineCoordinateMap (T.presheaf.germ ⊤ x trivial).hom = T.fromSpecStalk x := by
  have h := (isAffineOpen_top T).fromSpecStalk_eq_fromSpecStalk (x := x) trivial
  simpa only [IsAffineOpen.fromSpecStalk, IsAffineOpen.fromSpec_top, QuotientCoefficientMap.affineCoordinateMap] using! h

theorem specBaseCoefficientMap_fromSpecStalk :
    Spec.CoefficientCechComparison.specBaseCoefficientMap (T.fromSpecStalk x) = (T.presheaf.germ ⊤ x trivial).hom := by
  exact (congrArg Spec.CoefficientCechComparison.specBaseCoefficientMap (affineCoordinateMap_germ_eq_fromSpecStalk T x)).symm.trans
    (QuotientCoefficientMap.specBaseCoefficientMap_affineCoordinateMap (T.presheaf.germ ⊤ x trivial).hom)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.StalkCoordinateLocalization
