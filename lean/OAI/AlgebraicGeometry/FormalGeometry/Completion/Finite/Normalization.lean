import OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalBaseProperFiniteness

/-! # Normalization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.Normalization.Construction

noncomputable section

/-! # Completion: finiteness of the actual integral normalization factor -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

/-- Finiteness of actual proper global sections proves finiteness of the integral factor. -/
theorem proper_fromNormalization_finite_of_appTop {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [IsProper f] (hf : f.appTop.hom.Finite) : IsFinite f.fromNormalization := by
  have : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  have : IsIso f.toNormalization.appTop := Proper.Normalization.Construction.proper_toNormalization_appTop_isIso f
  apply (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mpr
  refine ⟨inferInstance, ?_⟩
  have he : f.fromNormalization.appTop = f.appTop ≫ inv f.toNormalization.appTop := by
    rw [← cancel_mono f.toNormalization.appTop, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, ← Scheme.Hom.comp_appTop, Scheme.Hom.toNormalization_fromNormalization]
  rw [he, CommRingCat.hom_comp]
  exact (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (inv f.toNormalization.appTop)).surjective).comp hf

/-- Over a normal affine base, the actual proper integral factor is finite. -/
theorem normal_base_proper_fromNormalization_finite (R : Type u) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [IsDominant f]
    [IsDomain Γ(X, ⊤)] [FormallyUnramified f.fromNormalization] : IsFinite f.fromNormalization :=
  proper_fromNormalization_finite_of_appTop f (NormalBaseProperFiniteness.Construction.normal_base_proper_appTop_finite R f)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Finite.Normalization.Construction
