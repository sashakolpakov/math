import OAI.NumberTheory.ArithmeticGroups.Lattices.StabilizerSaturation

/-! # Hom Coset Embedding -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.HomCosetEmbedding.Construction

noncomputable section

/-! A continuous group homomorphism whose orbit in a coset space is
closed gives a closed embedding of the corresponding source quotient. -/

open scoped Classical
open Set MulAction

def homSubgroupCosetMap {H K : Type*} [Group H] [Group K]
    (f : H →* K) (Γ : Subgroup K) : H ⧸ Γ.comap f → K ⧸ Γ :=
  Quotient.map' f fun x y hxy => by
    apply QuotientGroup.leftRel_apply.mpr
    have hm : x⁻¹ * y ∈ Γ.comap f := QuotientGroup.leftRel_apply.mp hxy
    simpa only [Subgroup.mem_comap, map_mul, map_inv] using hm

theorem homSubgroupCosetMap_closedEmbedding
    {H K : Type*} [Group H] [Group K]
    [TopologicalSpace H] [IsTopologicalGroup H] [SigmaCompactSpace H]
    [TopologicalSpace K] [IsTopologicalGroup K]
    (f : H →* K) (hf : Continuous f) (Γ : Subgroup K)
    [T2Space (K ⧸ Γ)] [LocallyCompactSpace (K ⧸ Γ)]
    (hclosed : IsClosed ((QuotientGroup.mk : K → K ⧸ Γ) '' Set.range f)) :
    Topology.IsClosedEmbedding (homSubgroupCosetMap f Γ) := by
  let : MulAction H (K ⧸ Γ) := MulAction.compHom (K ⧸ Γ) f
  let : ContinuousSMul H (K ⧸ Γ) := ⟨(hf.comp continuous_fst).smul continuous_snd⟩
  let q₀ := (QuotientGroup.mk (1 : K) : K ⧸ Γ)
  have horbit : orbit H q₀ = (QuotientGroup.mk : K → K ⧸ Γ) '' Set.range f := by
    ext q
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨f h, ⟨h, rfl⟩, ?_⟩
      change QuotientGroup.mk (f h) = QuotientGroup.mk (f h * 1)
      rw [mul_one]
    · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
      refine ⟨h, ?_⟩
      change QuotientGroup.mk (f h * 1) = QuotientGroup.mk (f h)
      rw [mul_one]
  have hs : stabilizer H q₀ = Γ.comap f := by
    ext h
    change f h • (QuotientGroup.mk (1 : K) : K ⧸ Γ) = QuotientGroup.mk 1 ↔ f h ∈ Γ
    simp [QuotientGroup.eq]
  have he := (ClosedOrbitQuotient.Construction.closed_orbit_quotient_embedding (G := H) q₀ (horbit.symm ▸ hclosed)).comp
    (ClosedOrbitQuotient.Construction.quotientHomeomorphOfEq hs.symm).isClosedEmbedding
  convert he using 1
  funext q
  obtain ⟨h, rfl⟩ := Quotient.exists_rep q
  rw [Function.comp_apply, ClosedOrbitQuotient.Construction.quotientHomeomorphOfEq_mk]
  change QuotientGroup.mk (f h) = QuotientGroup.mk (f h * 1)
  rw [mul_one]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.HomCosetEmbedding.Construction
