import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Principal Localization Cartesian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalLocalizationCartesian

noncomputable section

/-! Compatible principal localizations form actual Cartesian squares of affine schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem principalLocalization_isPullback
    {A B P Q : Type u} [CommRing A] [CommRing B] [CommRing P] [CommRing Q]
    [Algebra A B] [Algebra A P] [Algebra A Q] [Algebra B Q] [Algebra P Q]
    [IsScalarTower A B Q] [IsScalarTower A P Q]
    (a : A) [IsLocalization.Away a P] [IsLocalization.Away (algebraMap A B a) Q] :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap P Q)))
      (Spec.map (CommRingCat.ofHom (algebraMap B Q)))
      (Spec.map (CommRingCat.ofHom (algebraMap A P)))
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers a)) Q := by
    simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using
      (inferInstanceAs (IsLocalization.Away (algebraMap A B a) Q))
  have : Algebra.IsPushout A B P Q := Algebra.isPushout_of_isLocalization (Submonoid.powers a) P B Q
  exact (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout A B P Q)).flip

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalLocalizationCartesian
