import OAI.RepresentationTheory.Theta.Geometric.Finite.LatticeCongruence

/-! # Lattice Restriction Action -/

namespace OAI.RepresentationTheory.Theta.Geometric.LatticeRestrictionAction

noncomputable section

/-! A group preserving an actual additive lattice acts on that lattice
and on its finite quotients by literal restriction of its original maps. -/

variable {G V : Type*} [Group G] [AddCommGroup V]
    (ρ : G →* (V ≃ₗ[ℤ] V)) (L : AddSubgroup V)
    (hL : ∀ (g : G) (v : V), ρ g v ∈ L ↔ v ∈ L)

def latticeRestrictionEquiv (g : G) : L ≃ₗ[ℤ] L where
  toFun x := ⟨ρ g x.val, (hL g x.val).mpr x.property⟩
  invFun x := ⟨(ρ g).symm x.val, (hL g _).mp (by
    simpa only [LinearEquiv.apply_symm_apply] using x.property)⟩
  left_inv x := Subtype.ext ((ρ g).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((ρ g).apply_symm_apply x.val)
  map_add' x y := Subtype.ext ((ρ g).map_add x.val y.val)
  map_smul' n x := Subtype.ext ((ρ g).map_smul n x.val)

def latticeRestrictionAction : G →* (L ≃ₗ[ℤ] L) where
  toFun := latticeRestrictionEquiv ρ L hL
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
    change ρ (g * h) x.val = ρ g (ρ h x.val)
    rw [map_mul]
    rfl

theorem latticeRestrictionAction_apply (g : G) (x : L) :
    (latticeRestrictionAction ρ L hL g x).val = ρ g x.val := rfl

theorem latticeRestrictionAction_congruence (N : ℕ) (g : G) :
    g ∈ (Finite.LatticeCongruence.latticeModNAction N (latticeRestrictionAction ρ L hL)).ker ↔
      ∀ x ∈ L, ∃ y ∈ L, ρ g x - x = N • y := by
  rw [Finite.LatticeCongruence.latticeModNAction_ker]
  constructor
  · intro h x hx
    obtain ⟨y, hy⟩ := h ⟨x, hx⟩
    exact ⟨y.val, y.property, congrArg Subtype.val hy⟩
  · intro h x
    obtain ⟨y, hy, he⟩ := h x.val x.property
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩

end

end OAI.RepresentationTheory.Theta.Geometric.LatticeRestrictionAction
