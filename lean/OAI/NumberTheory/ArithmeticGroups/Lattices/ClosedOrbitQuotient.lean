import Mathlib

/-! # Closed Orbit Quotient -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ClosedOrbitQuotient.Construction

noncomputable section

/-! Closed continuous orbits of sigma-compact groups carry the quotient
topology of the group modulo the stabilizer. -/

open scoped Classical
open Set MulAction

def quotientHomeomorphOfEq {H : Type*} [Group H] [TopologicalSpace H]
    {Γ Δ : Subgroup H} (h : Γ = Δ) : (H ⧸ Γ) ≃ₜ (H ⧸ Δ) := by
  subst Δ
  exact Homeomorph.refl _

@[simp] theorem quotientHomeomorphOfEq_mk {H : Type*} [Group H] [TopologicalSpace H]
    {Γ Δ : Subgroup H} (h : Γ = Δ) (g : H) :
    quotientHomeomorphOfEq h (QuotientGroup.mk g) = QuotientGroup.mk g := by
  subst Δ
  rfl

theorem closed_orbit_quotient_embedding
    {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SigmaCompactSpace G] [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MulAction G X] [ContinuousSMul G X] (x : X) (hx : IsClosed (orbit G x)) :
    Topology.IsClosedEmbedding (ofQuotientStabilizer G x) := by
  let O := orbit G x
  let : LocallyCompactSpace O := hx.locallyCompactSpace
  let : ContinuousSMul G O := ⟨by
    apply Continuous.subtype_mk
    exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)⟩
  let x₀ : O := ⟨x, mem_orbit_self x⟩
  let e := (orbitEquivQuotientStabilizer G x).symm
  have hcomp : e ∘ (QuotientGroup.mk : G → G ⧸ stabilizer G x) = fun g => g • x₀ := by
    funext g
    apply Subtype.ext
    rfl
  have hecont : Continuous e := by
    apply (QuotientGroup.isQuotientMap_mk (stabilizer G x)).continuous_iff.mpr
    rw [hcomp]
    exact continuous_id.smul continuous_const
  have heopen : IsOpenMap e := by
    apply IsOpenMap.of_comp (QuotientGroup.continuous_mk (N := stabilizer G x))
      QuotientGroup.mk_surjective
    rw [hcomp]
    exact isOpenMap_smul_of_sigmaCompact x₀
  let h := e.toHomeomorphOfContinuousOpen hecont heopen
  exact hx.isClosedEmbedding_subtypeVal.comp h.isClosedEmbedding

def subgroupCosetMap {H : Type*} [Group H] (G Γ : Subgroup H) :
    G ⧸ Γ.subgroupOf G → H ⧸ Γ :=
  Quotient.map' (fun g : G => g.val) fun x y hxy => by
    apply QuotientGroup.leftRel_apply.mpr
    have hm : x⁻¹ * y ∈ Γ.subgroupOf G := QuotientGroup.leftRel_apply.mp hxy
    exact hm

@[simp] theorem subgroupCosetMap_mk {H : Type*} [Group H] (G Γ : Subgroup H) (g : G) :
    subgroupCosetMap G Γ (QuotientGroup.mk g) = QuotientGroup.mk g.val := rfl

theorem subgroupCosetMap_injective {H : Type*} [Group H] (G Γ : Subgroup H) :
    Function.Injective (subgroupCosetMap G Γ) := by
  intro a b
  obtain ⟨x, rfl⟩ := Quotient.exists_rep a
  obtain ⟨y, rfl⟩ := Quotient.exists_rep b
  intro he
  apply QuotientGroup.eq.mpr
  change (QuotientGroup.mk x.val : H ⧸ Γ) = QuotientGroup.mk y.val at he
  have hm : x.val⁻¹ * y.val ∈ Γ := QuotientGroup.eq.mp he
  exact hm

theorem continuous_subgroupCosetMap {H : Type*} [Group H] [TopologicalSpace H]
    (G Γ : Subgroup H) : Continuous (subgroupCosetMap G Γ) :=
  continuous_subtype_val.quotient_map' _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ClosedOrbitQuotient.Construction
