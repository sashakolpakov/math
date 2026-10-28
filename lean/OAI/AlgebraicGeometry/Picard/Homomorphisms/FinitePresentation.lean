import OAI.AlgebraicGeometry.Picard.Homomorphisms.Smooth

/-! # Finite Presentation -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.FinitePresentation.Construction

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency.types false in
/-- A morphism to a scheme locally of finite type over the base is locally
of finite presentation when its composite to the base is. -/
theorem locallyOfFinitePresentation_of_comp_of_finiteType
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (h : LocallyOfFinitePresentation (f ≫ g)) (hg : LocallyOfFiniteType g) :
    LocallyOfFinitePresentation f := by
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H := IsZariskiLocalAtTarget.restrict h U.1
    rw [morphismRestrict_comp] at H
    exact this H (IsZariskiLocalAtTarget.restrict hg U.1) U.2
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H := IsZariskiLocalAtSource.comp h (f ⁻¹ᵁ U.1).ι
    rw [← morphismRestrict_ι_assoc] at H
    exact this H (IsZariskiLocalAtSource.comp hg U.1.ι) U.2
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top X)]
    intro U
    have H := IsZariskiLocalAtSource.comp h U.1.ι
    rw [← Category.assoc] at H
    exact this H U.2
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)] at h ⊢
  have hg' := HasRingHomProperty.appTop (P := @LocallyOfFiniteType) g hg
  exact RingHom.FinitePresentation.of_comp_finiteType g.appTop.hom h hg'

set_option backward.isDefEq.respectTransparency.types false in
instance relativeFrobenius_locallyOfFinitePresentation
    (p : ℕ) (hp : p.Prime) {S : Scheme.{u}}
    (hS : (p : Γ(S, ⊤)) = 0) (A : Over S) [LocallyOfFinitePresentation A.hom] :
    LocallyOfFinitePresentation (Frobenius.Construction.relativeFrobenius p hp hS A).left := by
  have hcomp : LocallyOfFinitePresentation ((Frobenius.Construction.relativeFrobenius p hp hS A).left ≫
      (Frobenius.Construction.frobeniusTwist p hp hS A).hom) := by
    rw [Over.w]
    infer_instance
  have hft : LocallyOfFiniteType (Frobenius.Construction.frobeniusTwist p hp hS A).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd A.hom (Frobenius.Construction.absoluteFrobenius p hp S hS)))
  exact locallyOfFinitePresentation_of_comp_of_finiteType hcomp hft

end OAI.AlgebraicGeometry.Picard.Homomorphisms.FinitePresentation.Construction
