import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.Module

/-! # Submodule Orbit -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SubmoduleOrbit.Construction

noncomputable section

/-! Finite-index stabilizers of submodules containing a congruence submodule. -/

open scoped Classical Pointwise

@[instance_reducible]
def submoduleImageAction {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Group G]
    (ρ : G →* (M ≃ₗ[R] M)) : MulAction G (Submodule R M) where
  smul g L := L.map (ρ g).toLinearMap
  one_smul L := by
    change L.map (ρ 1).toLinearMap = L
    simp
  mul_smul g h L := by
    change L.map (ρ (g * h)).toLinearMap = (L.map (ρ h).toLinearMap).map (ρ g).toLinearMap
    rw [map_mul]
    exact Submodule.map_comp (ρ h).toLinearMap (ρ g).toLinearMap L

def submoduleImageStabilizer {R M G : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Group G]
    (ρ : G →* (M ≃ₗ[R] M)) (L : Submodule R M) : Subgroup G :=
  @MulAction.stabilizer G (Submodule R M) _ (submoduleImageAction ρ) L

theorem congruence_submodule_le_image
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (L : Submodule R M) (d : R) (hL : d • (⊤ : Submodule R M) ≤ L)
    (e : M ≃ₗ[R] M) : d • (⊤ : Submodule R M) ≤ L.map e.toLinearMap := by
  intro y hy
  obtain ⟨z, _, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists y d ⊤).mp hy
  refine ⟨d • e.symm z, hL (Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.mem_top)), ?_⟩
  simp

theorem submoduleImageStabilizer_finiteIndex
    {R M G : Type*} [CommRing R] [Ring.HasFiniteQuotients R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Group G]
    (ρ : G →* (M ≃ₗ[R] M)) (L : Submodule R M)
    (d : R) (hd : d ≠ 0) (hL : d • (⊤ : Submodule R M) ≤ L) :
    (submoduleImageStabilizer ρ L).FiniteIndex := by
  let : MulAction G (Submodule R M) := submoduleImageAction ρ
  let N : Submodule R M := d • ⊤
  let : Finite (M ⧸ N) := Lattices.Finite.Module.Construction.finite_quotient_element_smul d hd
  let : Finite (Set.Ici N) :=
    Finite.of_equiv (Submodule R (M ⧸ N)) N.comapMkQRelIso.toEquiv
  let f : MulAction.orbit G L → Set.Ici N := fun S => ⟨S.val, by
    obtain ⟨g, hg⟩ := S.property
    rw [← hg]
    exact congruence_submodule_le_image L d hL (ρ g)⟩
  let : Finite (MulAction.orbit G L) := Finite.of_injective f (fun x y h => by
    have hval : (f x).val = (f y).val := congrArg Subtype.val h
    exact Subtype.ext hval)
  let : Finite (G ⧸ MulAction.stabilizer G L) :=
    Finite.of_equiv (MulAction.orbit G L) (MulAction.orbitEquivQuotientStabilizer G L)
  change (MulAction.stabilizer G L).FiniteIndex
  exact Subgroup.finiteIndex_of_finite_quotient

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SubmoduleOrbit.Construction
