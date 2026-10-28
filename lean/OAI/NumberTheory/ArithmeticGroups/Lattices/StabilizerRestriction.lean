import OAI.NumberTheory.ArithmeticGroups.Lattices.SubmoduleOrbit

/-! # Stabilizer Restriction -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.StabilizerRestriction.Construction

noncomputable section

/-! Restriction of linear actions to invariant integral submodules. -/

open scoped Classical Pointwise

theorem submoduleImageStabilizer_mem_iff
    {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Group G]
    (ρ : G →* (M ≃ₗ[R] M)) (L : Submodule R M) (g : G) :
    g ∈ SubmoduleOrbit.Construction.submoduleImageStabilizer ρ L ↔ ∀ x, ρ g x ∈ L ↔ x ∈ L := by
  change L.map (ρ g).toLinearMap = L ↔ _
  constructor
  · intro h x
    constructor
    · intro hx
      rw [← h] at hx
      obtain ⟨y, hy, he⟩ := hx
      exact (ρ g).injective he ▸ hy
    · intro hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
  · intro h
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (h x).mpr hx
    · intro x hx
      refine ⟨(ρ g).symm x, (h _).mp ?_, (ρ g).apply_symm_apply x⟩
      simpa only [LinearEquiv.apply_symm_apply] using hx

def stabilizerRestriction
    {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Group G]
    (ρ : G →* (M ≃ₗ[R] M)) (L : Submodule R M) :
    SubmoduleOrbit.Construction.submoduleImageStabilizer ρ L →* (L ≃ₗ[R] L) where
  toFun g := (ρ g.val).ofSubmodules L L g.property
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change ρ 1 x.val = x.val
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    change ρ (g.val * h.val) x.val = ρ g.val (ρ h.val x.val)
    rw [map_mul]
    rfl

theorem stabilizerRestriction_apply
    {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Group G]
    (ρ : G →* (M ≃ₗ[R] M)) (L : Submodule R M)
    (g : SubmoduleOrbit.Construction.submoduleImageStabilizer ρ L) (x : L) :
    (stabilizerRestriction ρ L g x).val = ρ g.val x.val := rfl

theorem stabilizes_scalar_submodule_iff
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (e : M ≃ₗ[R] M) (L : Submodule R M) (d : R)
    (hd : Function.Injective (fun x : M => d • x)) :
    (d • L).map e.toLinearMap = d • L ↔ L.map e.toLinearMap = L := by
  let f : M →ₗ[R] M := DistribSMul.toLinearMap R M d
  have hcomm : e.toLinearMap.comp f = f.comp e.toLinearMap := by
    apply LinearMap.ext
    intro x
    exact e.map_smul d x
  change (L.map f).map e.toLinearMap = L.map f ↔ _
  rw [← Submodule.map_comp, hcomm, Submodule.map_comp]
  exact (Submodule.map_injective_of_injective hd).eq_iff

theorem restriction_stabilizes_iff
    {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Group G]
    (ρ : G →* (M ≃ₗ[R] M)) (Λ W : Submodule R M) (hW : W ≤ Λ)
    (g : SubmoduleOrbit.Construction.submoduleImageStabilizer ρ Λ) :
    (W.comap Λ.subtype).map (stabilizerRestriction ρ Λ g).toLinearMap = W.comap Λ.subtype ↔
      W.map (ρ g.val).toLinearMap = W := by
  have hcomp : Λ.subtype.comp (stabilizerRestriction ρ Λ g).toLinearMap =
      (ρ g.val).toLinearMap.comp Λ.subtype := by
    apply LinearMap.ext
    intro x
    rfl
  rw [← (Submodule.map_injective_of_injective Λ.injective_subtype).eq_iff,
    ← Submodule.map_comp, hcomp, Submodule.map_comp, Submodule.map_comap_subtype,
    inf_eq_right.mpr hW]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.StabilizerRestriction.Construction
