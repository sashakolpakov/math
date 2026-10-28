import OAI.AlgebraicGeometry.Albanese.Construction.ReducedFactor
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Immersion Factorization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ImmersionFactorization

noncomputable section

/-! On every reduced test scheme, an actual locally closed immersion
is detected by its underlying pointwise image. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem existsUnique_lift_immersion_of_range_subset
    {X Y Z : Scheme} (i : X ⟶ Z) [IsImmersion i] (f : Y ⟶ Z) [IsReduced Y]
    (h : Set.range f ⊆ Set.range i) : ∃! g : Y ⟶ X, g ≫ i = f := by
  let u := i.coborderRange.ι
  have hu : Set.range f ⊆ Set.range u := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := h ⟨y, rfl⟩
    refine ⟨i.liftCoborder x, ?_⟩
    exact (congrArg (fun q => q x) i.liftCoborder_ι).trans hx
  let l := IsOpenImmersion.lift u f hu
  have hl : l ≫ u = f := IsOpenImmersion.lift_fac u f hu
  have hr : Set.range l ⊆ Set.range i.liftCoborder := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := h ⟨y, rfl⟩
    refine ⟨x, ?_⟩
    apply u.isOpenEmbedding.injective
    exact (congrArg (fun q => q x) i.liftCoborder_ι).trans
      (hx.trans (congrArg (fun q => q y) hl).symm)
  let g := Albanese.Construction.ReducedFactor.factorThroughClosed i.liftCoborder l hr
  have hg : g ≫ i = f := by
    rw [← i.liftCoborder_ι, ← Category.assoc, Albanese.Construction.ReducedFactor.factorThroughClosed_comp]
    exact hl
  exact ⟨g, hg, fun q hq => (cancel_mono i).mp (hq.trans hg.symm)⟩

theorem reduced_immersion_lift_iff_range
    {X Y Z : Scheme} (i : X ⟶ Z) [IsImmersion i] (f : Y ⟶ Z) [IsReduced Y] :
    (∃! g : Y ⟶ X, g ≫ i = f) ↔ Set.range f ⊆ Set.range i := by
  constructor
  · rintro ⟨g, hg, _⟩ _ ⟨y, rfl⟩
    exact ⟨g y, congrArg (fun q => q y) hg⟩
  · exact existsUnique_lift_immersion_of_range_subset i f

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Reduced.ImmersionFactorization
