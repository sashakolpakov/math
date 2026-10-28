import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.Normalization
import OAI.AlgebraicGeometry.FormalGeometry.Completion.StalkFlat

/-! # Normalized Local Functions -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedLocalFunctions.Construction

noncomputable section

/-!
# Completion: actual global functions of the normalized family over its local base

The relative normalization's affine coordinate identifications combine
with flat localization at the chosen point. The resulting family over
the actual stalk ring has that base ring as its actual global functions.
The original base need not be affine.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

/-- The first normalization factor induces an isomorphism over the actual normalization affine charts. -/
theorem proper_toNormalization_app_preimage_isIso (U : Y.Opens) (hU : IsAffineOpen U) :
    IsIso (f.toNormalization.app (f.fromNormalization ⁻¹ᵁ U)) := by
  have he : f.toNormalization ⁻¹ᵁ f.fromNormalization ⁻¹ᵁ U = f ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]
  have h : (Proper.Normalization.Construction.properNormalizationSectionIso f U hU).hom ≫
      X.presheaf.map (eqToHom he).op = f.toNormalization.app (f.fromNormalization ⁻¹ᵁ U) := by
    rw [Proper.Normalization.Construction.properNormalizationSectionIso_hom, Scheme.Hom.appLE_map, ← Scheme.Hom.app_eq_appLE]
  rw [← h]
  infer_instance

/-- The original normalization map base-changed to the actual local ring of its target. -/
def normalizedLocalFamily (n : f.normalization) :
    pullback f.toNormalization (f.normalization.fromSpecStalk n) ⟶
      Spec (f.normalization.presheaf.stalk n) :=
  pullback.snd _ _

instance normalizedLocalFamily_isProper (n : f.normalization) :
    IsProper (normalizedLocalFamily f n) := by
  have := Proper.Normalization.Construction.proper_toNormalization f
  unfold normalizedLocalFamily
  infer_instance

/-- The actual normalized local family has exactly its base's global functions. -/
theorem normalizedLocalFamily_appTop_isIso (n : f.normalization) :
    IsIso (normalizedLocalFamily f n).appTop := by
  let g := f.normalization.fromSpecStalk n
  have : Flat g := StalkFlat.Construction.scheme_fromSpecStalk_flat f.normalization n
  have : IsProper f.toNormalization := Proper.Normalization.Construction.proper_toNormalization f
  obtain ⟨_, ⟨U, hU, rfl⟩, hn, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f.fromNormalization n)) isOpen_univ
  let W := f.fromNormalization ⁻¹ᵁ U
  have hW : IsAffineOpen W := hU.preimage f.fromNormalization
  have hg : g ⁻¹ᵁ W = ⊤ := StalkFlat.Construction.scheme_fromSpecStalk_preimage_eq_top _ n W hn
  have hUT : ⊤ ≤ g ⁻¹ᵁ W := hg.ge
  have hpre : pullback.fst f.toNormalization g ⁻¹ᵁ f.toNormalization ⁻¹ᵁ W = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage, hg,
      TopologicalSpace.Opens.map_top]
  have hUY : (⊤ : (pullback f.toNormalization g).Opens) =
      pullback.fst f.toNormalization g ⁻¹ᵁ f.toNormalization ⁻¹ᵁ W ⊓
        pullback.snd f.toNormalization g ⁻¹ᵁ ⊤ := by simp [hpre]
  have hi := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback f.toNormalization g) hUT le_rfl hUY hW (isAffineOpen_top _)
    (f.toNormalization.isCompact_preimage hW.isCompact)
    (f.toNormalization.isQuasiSeparated_preimage hW.isQuasiSeparated)
  have hs := (isIso_pushoutSection_iff (IsPullback.of_hasPullback f.toNormalization g)
    hUT le_rfl hUY).mp hi
  have : IsIso (f.toNormalization.appLE W (f.toNormalization ⁻¹ᵁ W) le_rfl) := by
    rw [← Scheme.Hom.app_eq_appLE]
    exact proper_toNormalization_app_preimage_isIso f U hU
  have ht := hs.isIso_inr_of_isIso
  simpa only [normalizedLocalFamily, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
    TopologicalSpace.Opens.map_top] using ht

/-- The global-function identification uses the actual local-family structure map. -/
def normalizedLocalFamilyGlobalFunctionsIso (n : f.normalization) :
    f.normalization.presheaf.stalk n ≅
      Γ(pullback f.toNormalization (f.normalization.fromSpecStalk n), ⊤) := by
  have := normalizedLocalFamily_appTop_isIso f n
  exact (Scheme.ΓSpecIso _).symm ≪≫ asIso (normalizedLocalFamily f n).appTop

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.NormalizedLocalFunctions.Construction
