import OAI.NumberTheory.ArithmeticGroups.Lattices.QuotientMeasure

/-! # Coset Map Inclusion -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CosetMapInclusion.Construction

noncomputable section

/-! Maps between coset spaces when a homomorphism sends one subgroup
into another, without assuming either subgroup is normal. -/

def cosetMapOfInclusion
    {H K : Type*} [Group H] [Group K]
    (f : H →* K) (Γ : Subgroup H) (Δ : Subgroup K) (h : Γ ≤ Δ.comap f) :
    H ⧸ Γ → K ⧸ Δ :=
  Quotient.map' f fun x y hxy => by
    apply QuotientGroup.leftRel_apply.mpr
    have hm := h (QuotientGroup.leftRel_apply.mp hxy)
    simpa only [Subgroup.mem_comap, map_mul, map_inv] using hm

theorem cosetMapOfInclusion_mk
    {H K : Type*} [Group H] [Group K]
    (f : H →* K) (Γ : Subgroup H) (Δ : Subgroup K) (h : Γ ≤ Δ.comap f) (g : H) :
    cosetMapOfInclusion f Γ Δ h (QuotientGroup.mk g) = QuotientGroup.mk (f g) := rfl

theorem continuous_cosetMapOfInclusion
    {H K : Type*} [Group H] [Group K] [TopologicalSpace H] [TopologicalSpace K]
    (f : H →* K) (hf : Continuous f) (Γ : Subgroup H) (Δ : Subgroup K) (h : Γ ≤ Δ.comap f) :
    Continuous (cosetMapOfInclusion f Γ Δ h) := hf.quotient_map' _

theorem cosetMapOfInclusion_range
    {H K : Type*} [Group H] [Group K]
    (f : H →* K) (Γ : Subgroup H) (Δ : Subgroup K) (h : Γ ≤ Δ.comap f) :
    Set.range (cosetMapOfInclusion f Γ Δ h) =
      Set.range (fun g : H => (QuotientGroup.mk (f g) : K ⧸ Δ)) := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨g, rfl⟩ := Quotient.exists_rep x
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨QuotientGroup.mk g, rfl⟩

theorem compact_closure_coset_image_of_representatives
    {H K : Type*} [Group H] [Group K] [TopologicalSpace K]
    (f : H →* K) (Δ : Subgroup K) [T2Space (K ⧸ Δ)]
    (C : Set K) (hC : IsCompact C)
    (hrep : ∀ g : H, ∃ γ ∈ Δ, f g * γ ∈ C) :
    IsCompact (closure (Set.range (fun g : H => (QuotientGroup.mk (f g) : K ⧸ Δ)))) := by
  have hcompact : IsCompact ((QuotientGroup.mk : K → K ⧸ Δ) '' C) :=
    hC.image (QuotientGroup.continuous_mk (N := Δ))
  apply hcompact.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hcompact.isClosed
  rintro _ ⟨g, rfl⟩
  obtain ⟨γ, hγ, hγC⟩ := hrep g
  exact ⟨f g * γ, hγC, QuotientGroup.mk_mul_of_mem (f g) hγ⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CosetMapInclusion.Construction
