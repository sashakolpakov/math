import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.FlatSections
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-! # Structure Sheaf Base Change -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.StructureSheafBaseChange.Construction

noncomputable section

/-! Flat base change preserves the actual structure-sheaf isomorphism of a proper morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {Z A Y : Scheme.{u}} (c : Z ⟶ A) [IsProper c] (a : Y ⟶ A) [Flat a]
  (hc : ∀ U : A.Opens, IsAffineOpen U → IsIso (c.app U))

include hc in
theorem proper_flat_pullback_app_isIso_on_chart (U : A.Opens) (hU : IsAffineOpen U)
    (V : Y.Opens) (hV : IsAffineOpen V) (hVU : V ≤ a ⁻¹ᵁ U) :
    IsIso ((pullback.snd c a).app V) := by
  let H := IsPullback.of_hasPullback c a
  have hW : pullback.snd c a ⁻¹ᵁ V =
      pullback.fst c a ⁻¹ᵁ c ⁻¹ᵁ U ⊓ pullback.snd c a ⁻¹ᵁ V := by
    simp_rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]
  have hi := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H hVU le_rfl hW hU hV
    (c.isCompact_preimage hU.isCompact) (c.isQuasiSeparated_preimage hU.isQuasiSeparated)
  have hp := (isIso_pushoutSection_iff H hVU le_rfl hW).mp hi
  have : IsIso (c.appLE U (c ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.appLE_eq_app]
    exact hc U hU
  have ht := hp.isIso_inr_of_isIso
  change IsIso ((pullback.snd c a).appLE V (pullback.snd c a ⁻¹ᵁ V) le_rfl) at ht
  rw [Scheme.Hom.appLE_eq_app] at ht
  exact ht

include hc in
/-- The full actual ring-sheaf map is an isomorphism after arbitrary flat base change. -/
theorem proper_flat_pullback_ringSheaf_isIso : IsIso (pullback.snd c a).toRingCatSheafHom := by
  let B := {V : Y.Opens // IsAffineOpen V ∧ ∃ U : A.Opens, IsAffineOpen U ∧ V ≤ a ⁻¹ᵁ U}
  have hB : Opens.IsBasis (Set.range (fun V : B => V.val)) := by
    apply Opens.isBasis_iff_nbhd.mpr
    intro W y hy
    obtain ⟨_, ⟨U, hU, rfl⟩, hay, _⟩ :=
      A.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (a y)) isOpen_univ
    have hy' : y ∈ W ⊓ a ⁻¹ᵁ U := ⟨hy, hay⟩
    obtain ⟨_, ⟨V, hV, rfl⟩, hyv, hv⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy' (W ⊓ a ⁻¹ᵁ U).isOpen
    exact ⟨V, ⟨⟨V, hV, U, hU, hv.trans inf_le_right⟩, rfl⟩, hyv, hv.trans inf_le_left⟩
  apply TopCat.Sheaf.isIso_iff_isIso_basis hB
  intro V
  obtain ⟨U, hU, hVU⟩ := V.property.2
  have hi := proper_flat_pullback_app_isIso_on_chart c a hc U hU V.val V.property.1 hVU
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact (ConcreteCategory.isIso_iff_bijective ((pullback.snd c a).app V.val)).mp hi

include hc in
/-- Every actual section map, including global sections, remains an isomorphism. -/
theorem proper_flat_pullback_app_isIso (V : Y.Opens) : IsIso ((pullback.snd c a).app V) := by
  have hs : IsIso (pullback.snd c a).toRingCatSheafHom :=
    proper_flat_pullback_ringSheaf_isIso c a hc
  let e := @asIso _ _ _ _ (pullback.snd c a).toRingCatSheafHom hs
  let e' := (sheafToPresheaf _ _).mapIso e
  have hi : IsIso ((pullback.snd c a).toRingCatSheafHom.hom.app (op V)) := (e'.app (op V)).isIso_hom
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact (ConcreteCategory.isIso_iff_bijective
    ((pullback.snd c a).toRingCatSheafHom.hom.app (op V))).mp hi

include hc in
/-- The global-section conclusion applies to any actual pullback square. -/
theorem proper_flat_isPullback_appTop_isIso {W : Scheme.{u}}
    {u : W ⟶ Z} {v : W ⟶ Y} (H : IsPullback u v c a) : IsIso v.appTop := by
  have : IsIso (pullback.snd c a).appTop := proper_flat_pullback_app_isIso c a hc ⊤
  rw [← H.isoPullback_hom_snd, Scheme.Hom.comp_appTop]
  infer_instance

include hc in
/-- Flat base change preserves section rings in any actual Cartesian square. -/
theorem proper_flat_isPullback_app_isIso {W : Scheme.{u}}
    {u : W ⟶ Z} {v : W ⟶ Y} (H : IsPullback u v c a) (V : Y.Opens) :
    IsIso (v.app V) := by
  have : IsIso ((pullback.snd c a).app V) := proper_flat_pullback_app_isIso c a hc V
  rw [← H.isoPullback_hom_snd, Scheme.Hom.comp_app]
  infer_instance

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.StructureSheafBaseChange.Construction
