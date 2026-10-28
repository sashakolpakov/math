import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.PropertyComparison
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Monomorphism Local Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomorphismLocalSections

noncomputable section

/-! A scheme monomorphism with local sections on target neighborhoods of its image is an open immersion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def monomorphismPullbackSectionIso {X Y : Scheme.{u}} (i : X ⟶ Y) [Mono i]
    (U : Y.Opens) (s : U.toScheme ⟶ X) (hs : s ≫ i = U.ι) : pullback i U.ι ≅ U.toScheme := by
  let t : U.toScheme ⟶ pullback i U.ι := pullback.lift s (𝟙 _) (hs.trans (Category.id_comp _).symm)
  have ht : t ≫ pullback.snd i U.ι = 𝟙 _ := pullback.lift_snd _ _ _
  refine ⟨pullback.snd i U.ι, t, ?_, ht⟩
  apply (cancel_mono (pullback.snd i U.ι)).mp
  rw [Category.assoc, ht, Category.comp_id, Category.id_comp]

theorem monomorphism_restrict_open_of_section {X Y : Scheme.{u}} (i : X ⟶ Y) [Mono i]
    (U : Y.Opens) (s : U.toScheme ⟶ X) (hs : s ≫ i = U.ι) : IsOpenImmersion (i ∣_ U) := by
  have : IsIso (pullback.snd i U.ι) := (monomorphismPullbackSectionIso i U s hs).isIso_hom
  exact (Cartesian.PropertyComparison.property_cartesian_iff_pullback (@IsOpenImmersion : MorphismProperty Scheme.{u})
    _ _ i U.ι (isPullback_morphismRestrict i U).flip).mpr inferInstance

theorem monomorphism_open_of_local_sections {X Y : Scheme.{u}} (i : X ⟶ Y) [Mono i]
    (h : ∀ x : X, ∃ U : Y.Opens, i x ∈ U ∧ ∃ s : U.toScheme ⟶ X, s ≫ i = U.ι) :
    IsOpenImmersion i := by
  choose U hx s hs using h
  apply IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsOpenImmersion) U
  · rintro y ⟨x, rfl⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  · intro x
    exact monomorphism_restrict_open_of_section i (U x) (s x) (hs x)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomorphismLocalSections
