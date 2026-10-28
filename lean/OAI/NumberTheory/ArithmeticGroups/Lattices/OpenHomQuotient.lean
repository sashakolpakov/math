import OAI.NumberTheory.ArithmeticGroups.Lattices.CosetMapInclusion

/-! # Open Hom Quotient -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OpenHomQuotient.Construction

noncomputable section

/-! A continuous open surjective homomorphism identifies a quotient
by a subgroup's inverse image with the quotient by that subgroup. -/

open scoped Classical

def homComapCosetEquiv
    {G H : Type*} [Group G] [Group H] (f : G →* H) (hf : Function.Surjective f)
    (Γ : Subgroup H) : (G ⧸ Γ.comap f) ≃ (H ⧸ Γ) :=
  Equiv.ofBijective (CosetMapInclusion.Construction.cosetMapOfInclusion f (Γ.comap f) Γ le_rfl) ⟨by
    intro a b
    obtain ⟨x, rfl⟩ := Quotient.exists_rep a
    obtain ⟨y, rfl⟩ := Quotient.exists_rep b
    intro h
    apply QuotientGroup.eq.mpr
    have he : (f x)⁻¹ * f y ∈ Γ := QuotientGroup.eq.mp h
    change f (x⁻¹ * y) ∈ Γ
    simpa only [map_mul, map_inv] using he, by
    intro q
    obtain ⟨y, rfl⟩ := Quotient.exists_rep q
    obtain ⟨x, rfl⟩ := hf y
    exact ⟨QuotientGroup.mk x, rfl⟩⟩

def openHomComapCosetHomeomorph
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : G →* H) (hsurj : Function.Surjective f) (hf : Continuous f) (hopen : IsOpenMap f)
    (Γ : Subgroup H) : (G ⧸ Γ.comap f) ≃ₜ (H ⧸ Γ) := by
  let e := homComapCosetEquiv f hsurj Γ
  have hecont : Continuous e := CosetMapInclusion.Construction.continuous_cosetMapOfInclusion f hf (Γ.comap f) Γ le_rfl
  have heopen : IsOpenMap e := by
    apply IsOpenMap.of_comp (QuotientGroup.continuous_mk (N := Γ.comap f))
      QuotientGroup.mk_surjective
    exact QuotientGroup.isOpenMap_coe.comp hopen
  exact e.toHomeomorphOfContinuousOpen hecont heopen

theorem open_surjective_hom_comap_quotient_compact
    {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : G →* H) (hsurj : Function.Surjective f) (hf : Continuous f) (hopen : IsOpenMap f)
    (Γ : Subgroup H) [CompactSpace (H ⧸ Γ)] : CompactSpace (G ⧸ Γ.comap f) :=
  (openHomComapCosetHomeomorph f hsurj hf hopen Γ).symm.compactSpace

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OpenHomQuotient.Construction
