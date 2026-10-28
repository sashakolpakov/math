import OAI.ArithmeticGeometry.Models.SpreadingOut.Image

/-! # Local Closure -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.LocalClosure.Construction

noncomputable section

/-! Closed conditions on an open ambient chart persist under reduced
schematic closure. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem range_morphism_restrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Set.range (f ∣_ U) = U.ι ⁻¹' Set.range f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, (morphismRestrict_base_coe f U x).symm⟩
  · rintro ⟨x, hx⟩
    let z : (f ⁻¹ᵁ U).toScheme := ⟨x, by
      change f x ∈ U
      rw [hx]
      exact y.property⟩
    refine ⟨z, Subtype.ext ?_⟩
    exact (morphismRestrict_base_coe f U z).trans hx

theorem image_restrict_range_eq_closure
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] (U : Y.Opens) :
    Set.range (f.imageι ∣_ U) = closure (Set.range (f ∣_ U)) := by
  rw [range_morphism_restrict, range_morphism_restrict,
    Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker]
  exact U.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
    U.ι.continuous (Set.range f)

/-- A reduced schematic closure satisfies each closed condition that the
original scheme satisfies on a chosen open ambient chart. -/
theorem image_restrict_factors_through_closed
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [IsReduced X]
    (U : Y.Opens) {Z : Scheme.{u}} (i : Z ⟶ U.toScheme) [IsClosedImmersion i]
    (h : Set.range (f ∣_ U) ⊆ Set.range i) :
    ∃ l : (f.imageι ⁻¹ᵁ U).toScheme ⟶ Z, l ≫ i = f.imageι ∣_ U := by
  have : IsReduced f.image := Image.Construction.schematic_image_reduced f
  apply Image.Construction.reduced_factors_through_closed_immersion
  rw [image_restrict_range_eq_closure]
  exact closure_minimal h i.isClosedEmbedding.isClosed_range

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.LocalClosure.Construction
