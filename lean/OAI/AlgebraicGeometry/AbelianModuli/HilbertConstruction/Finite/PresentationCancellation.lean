import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Presentation Cancellation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.PresentationCancellation

noncomputable section

/-! Finite presentation of a composite descends to the first map when the second map is locally of finite type. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem locallyFinitePresentation_of_comp_of_locallyFiniteType
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hfg : LocallyOfFinitePresentation (f ≫ g)) (hg : LocallyOfFiniteType g) :
    LocallyOfFinitePresentation f := by
  let : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFinitePresentation.{u})
      (Q := RingHom.FinitePresentation)
  let : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
      (Q := RingHom.FinitePresentation)
  let : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFiniteType.{u})
      (Q := RingHom.FiniteType)
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H := IsZariskiLocalAtTarget.restrict hfg U.1
    rw [morphismRestrict_comp] at H
    exact this H (IsZariskiLocalAtTarget.restrict hg U.1) inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion
      (@LocallyOfFinitePresentation) (f ⁻¹ᵁ U.1).ι (f ≫ g) hfg
    rw [← morphismRestrict_ι_assoc] at H
    exact this H (HasRingHomProperty.comp_of_isOpenImmersion
      (@LocallyOfFiniteType) U.1.ι g hg) inferInstance
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top X)]
    intro U
    have H := HasRingHomProperty.comp_of_isOpenImmersion
      (@LocallyOfFinitePresentation) U.1.ι (f ≫ g) hfg
    rw [← Category.assoc] at H
    exact this H inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)] at hfg ⊢
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)] at hg
  have H : (f.appTop.hom.comp g.appTop.hom).FinitePresentation := by
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using hfg
  exact H.of_comp_finiteType g.appTop.hom hg

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.PresentationCancellation
