import OAI.NumberTheory.PadicHodge.IntegralComparison.Intrinsic.PointParameterSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.SectionPuncturePullback
import OAI.NumberTheory.PadicHodge.IntegralComparison.ComplementaryAffineCover
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.AffineCommonCover

/-! # Point Parameter Cover -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PointParameterCover

noncomputable section

/-! Concatenated ambient point equations give the genuine punctured
principal cover on the closed subscheme, and its complementary cover. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y T : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
  (s₀ : T ⟶ X) [IsClosedImmersion s₀]
  (U : Y.Opens) (hU : IsAffineOpen U)
  {c g : ℕ} (s : Fin c → Γ(Y, U)) (t : Fin g → Γ(Y, U))
  (hs : Ideal.span (Set.range s) = i.ker.ideal ⟨U, hU⟩)
  (hst : Ideal.span (Set.range (Fin.append s t)) = (s₀ ≫ i).ker.ideal ⟨U, hU⟩)

include hs hst in
theorem source_ideal : Ideal.span (Set.range (fun j => i.app U (t j))) =
    s₀.ker.ideal ⟨i ⁻¹ᵁ U, hU.preimage i⟩ := by
  have hk : (RingHom.ker (i.app U).hom).map (i.app U).hom = ⊥ := by
    apply le_antisymm _ bot_le
    rw [Ideal.map_le_iff_le_comap]
    exact le_rfl
  have h := congrArg (Ideal.map (i.app U).hom) hst
  rw [CompositeSectionKernel.range_append, Ideal.span_union, Ideal.map_sup,
    hs, Scheme.Hom.ker_apply, hk, bot_sup_eq, Ideal.map_span, ← Set.range_comp] at h
  have he : RingHom.ker ((s₀ ≫ i).app U).hom =
      Ideal.comap (i.app U).hom (RingHom.ker (s₀.app (i ⁻¹ᵁ U)).hom) := by
    rw [RingHom.comap_ker]
    rfl
  rw [Scheme.Hom.ker_apply, he, Ideal.map_comap_of_surjective _ (i.app_surjective U hU)] at h
  rw [Scheme.Hom.ker_apply]
  change Ideal.span (Set.range ((i.app U).hom ∘ t)) =
    RingHom.ker (s₀.app (i ⁻¹ᵁ U)).hom
  exact h

theorem outside : i ⁻¹ᵁ SectionIdealPuncturedCover.outside (s₀ ≫ i).ker =
    SectionIdealPuncturedCover.outside s₀.ker :=
  SectionPuncturePullback.outside i (𝟙 T) (s₀ ≫ i) s₀ (Category.id_comp _).symm
    i.isClosedEmbedding.injective (by intro x; exact ⟨x, rfl⟩)

include hs hst in
theorem principal_cover : (⨆ j, i ⁻¹ᵁ (U ⊓ Y.basicOpen (t j))) =
    i ⁻¹ᵁ U ⊓ SectionIdealPuncturedCover.outside s₀.ker := by
  have h := SectionIdealPuncturedCover.cover s₀.ker (i ⁻¹ᵁ U) (hU.preimage i)
    (fun j => i.app U (t j)) (source_ideal i s₀ U hU s t hs hst)
  rw [h]
  congr 1
  funext j
  rw [inf_eq_right.mpr (Y.basicOpen_le (t j)), Scheme.preimage_basicOpen]

theorem complementary_cover :
    (⨆ j, i ⁻¹ᵁ (U ⊓ ComplementaryAffineCover.opens
      (SectionIdealPuncturedCover.outside (s₀ ≫ i).ker) j)) =
        i ⁻¹ᵁ U ⊓ SectionIdealPuncturedCover.outside s₀.ker := by
  rw [← i.preimage_iSup, ← inf_iSup_eq, ComplementaryAffineCover.covers,
    i.preimage_inf, outside]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.PointParameterCover
