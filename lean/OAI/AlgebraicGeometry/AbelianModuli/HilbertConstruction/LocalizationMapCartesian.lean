import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrincipalLocalizationCartesian

/-! # Localization Map Cartesian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocalizationMapCartesian

noncomputable section

/-! The canonical map between principal localizations is the base change of the original affine morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem localizationMap_isPullback {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (a : A) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (IsLocalization.Away.map
        (Localization.Away a) (Localization.Away (φ a)) φ a)))
      (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (φ a)))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a))))
      (Spec.map (CommRingCat.ofHom φ)) := by
  let : Algebra A B := φ.toAlgebra
  let P := Localization.Away a
  let Q := Localization.Away (φ a)
  let : Algebra P Q := (IsLocalization.Away.map P Q φ a).toAlgebra
  have : IsScalarTower A P Q := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change algebraMap B Q (φ r) = IsLocalization.Away.map P Q φ a (algebraMap A P r)
    simp only [IsLocalization.Away.map, IsLocalization.map_eq]
  exact PrincipalLocalizationCartesian.principalLocalization_isPullback (A := A) (B := B) (P := P) (Q := Q) a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocalizationMapCartesian
