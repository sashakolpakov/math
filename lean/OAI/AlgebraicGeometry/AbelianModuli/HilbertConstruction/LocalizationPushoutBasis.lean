import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.BasisTransport
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.Localization.BaseChange

/-! # Localization Pushout Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocalizationPushoutBasis

noncomputable section

/-! A finite basis of a canonical localization transports across a ring pushout whose base map is that localization. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u

def localizationPushoutBasis {R A S B : Type u}
    [CommRing R] [CommRing A] [CommRing S] [CommRing B]
    (f : R →+* A) (g : R →+* S) (k : A →+* B) (l : S →+* B)
    (h : IsPushout (CommRingCat.ofHom g) (CommRingCat.ofHom f)
      (CommRingCat.ofHom l) (CommRingCat.ofHom k)) (T : Submonoid R)
    (hS : @IsLocalization R _ T S _ g.toAlgebra) {ι : Type*}
    (b : @Module.Basis ι (Localization T) (@LocalizedModule R _ T A _ f.toModule)
      _ _ inferInstance) : @Module.Basis ι S B _ _ l.toModule := by
  letI : Algebra R A := f.toAlgebra
  letI : Algebra R S := g.toAlgebra
  letI : Algebra A B := k.toAlgebra
  letI : Algebra S B := l.toAlgebra
  letI : Algebra R B := (k.comp f).toAlgebra
  haveI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom h.w.symm)
  haveI : IsLocalization T S := hS
  have hp : Algebra.IsPushout R S A B := CommRingCat.isPushout_iff_isPushout.mp h
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A T) B :=
    (Algebra.isLocalization_iff_isPushout T S).mpr hp.symm
  exact Localized.BasisTransport.localizedBasisTransport T (IsScalarTower.toAlgHom R A B).toLinearMap b

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocalizationPushoutBasis
