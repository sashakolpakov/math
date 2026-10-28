import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Normalization -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.Normalization.Construction

noncomputable section

/-!
# Completion: the relative normalization of a proper morphism

Properness makes every section over an affine base open integral. The
relative normalization therefore has precisely those sections as its
coordinate algebra. The map to the normalization is proper and surjective.
Geometric connectedness of its fibers is a further obligation.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Over any affine base open, properness makes the map on sections integral. -/
theorem universallyClosed_app_isIntegral [UniversallyClosed f]
    (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).hom.IsIntegral := by
  have : IsAffine U.toScheme := hU
  have h := isIntegral_appTop_of_universallyClosed (f ∣_ U)
  rw [morphismRestrict_appTop, CommRingCat.hom_comp,
    RingHom.isIntegral_respectsIso.cancel_right_isIso] at h
  have h' : (Scheme.Hom.app f (U.ι ''ᵁ ⊤)).hom.IsIntegral := h
  rw [Scheme.Opens.ι_image_top] at h'
  exact h'

variable [IsProper f]

/-- The first factor of the actual relative normalization remains proper. -/
theorem proper_toNormalization : IsProper f.toNormalization := by
  have : IsProper (f.toNormalization ≫ f.fromNormalization) := by
    rwa [Scheme.Hom.toNormalization_fromNormalization]
  exact IsProper.of_comp f.toNormalization f.fromNormalization

/-- The proper dominant first factor is surjective. -/
theorem proper_toNormalization_surjective : Surjective f.toNormalization := by
  let := proper_toNormalization f
  constructor
  exact Set.range_eq_univ.mp (by
    rw [← f.toNormalization.isClosedMap.isClosed_range.closure_eq]
    exact f.toNormalization.denseRange.closure_range)

/-- The integral closure defining the proper normalization is the whole section ring. -/
theorem proper_normalization_integralClosure_eq_top (U : Y.Opens) (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U) = ⊤ := by
  let := (f.app U).hom.toAlgebra
  rw [integralClosure_eq_top_iff, ← algebraMap_isIntegral_iff, RingHom.algebraMap_toAlgebra]
  exact universallyClosed_app_isIntegral f U hU

/-- The relative normalization's coordinate algebra is the original section ring. -/
def properNormalizationSectionIso (U : Y.Opens) (hU : IsAffineOpen U) :
    Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) ≅ Γ(X, f ⁻¹ᵁ U) := by
  letI := (f.app U).hom.toAlgebra
  refine f.normalizationObjIso hU ≪≫
    (RingEquiv.ofBijective
      (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)).val.toRingHom ?_).toCommRingCatIso
  refine ⟨Subtype.val_injective, fun s => ⟨⟨s, ?_⟩, rfl⟩⟩
  rw [proper_normalization_integralClosure_eq_top f U hU]
  trivial

/-- The coordinate-ring identification is the actual map of the normalization factor. -/
theorem properNormalizationSectionIso_hom (U : Y.Opens) (hU : IsAffineOpen U) :
    (properNormalizationSectionIso f U hU).hom =
      f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ U) (f ⁻¹ᵁ U)
        (by simp [← Scheme.Hom.comp_preimage]) := by
  exact f.normalizationObjIso_hom_val hU

/-- Over an affine base, the map to the normalization induces an isomorphism on
the actual global section rings. -/
theorem proper_toNormalization_appTop_isIso [IsAffine Y] : IsIso f.toNormalization.appTop := by
  have h := (properNormalizationSectionIso f ⊤ (isAffineOpen_top Y)).isIso_hom
  rw [properNormalizationSectionIso_hom] at h
  simpa only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
    TopologicalSpace.Opens.map_top] using h

/-- When a proper map to an affine scheme already has the base's global functions,
its relative normalization is the base itself. -/
theorem proper_fromNormalization_isIso_of_appTop [IsAffine Y] [IsIso f.appTop] :
    IsIso f.fromNormalization := by
  have : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  have := proper_toNormalization_appTop_isIso f
  have : IsIso f.fromNormalization.appTop := by
    rw [← isIso_comp_right_iff _ f.toNormalization.appTop]
    rw [← Scheme.Hom.comp_appTop, Scheme.Hom.toNormalization_fromNormalization]
    infer_instance
  apply (HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme)).mpr
  exact ⟨inferInstance, inferInstance⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.Normalization.Construction
