import OAI.AlgebraicGeometry.GroupSchemes.Tower
import OAI.AlgebraicGeometry.GroupSchemes.CoordinateMaps

/-! # Nontrivial Multiplication -/

namespace OAI.AlgebraicGeometry.GroupSchemes

noncomputable section

/-! The prescribed rank growth forces nonzero multiplication at every step. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite WithConv _root_.CategoryTheory.MonObj

universe u
variable {k : Type u} [Field k]
variable {p : ℕ} [Fact p.Prime]

/-- The next level is not already killed by the preceding level's exponent. -/
theorem FiniteEtale.PDivisibleGroup.identity_power_ne_one (G : FiniteEtale.PDivisibleGroup k p 1) (n : ℕ) :
    (𝟙 (G.level (n + 1)).scheme) ^ (p ^ n) ≠ 1 := by
  intro hzero
  obtain ⟨r, hr⟩ := (G.kernel n (G.level (n + 1)).algebra (𝟙 _)).mpr hzero
  have he := congrArg (fun f : (G.level (n + 1)).scheme ⟶ (G.level (n + 1)).scheme =>
    FiniteEtale.FiniteCommGroupScheme.coordinateMap f) hr
  rw [FiniteEtale.FiniteCommGroupScheme.coordinateMap_comp, FiniteEtale.FiniteCommGroupScheme.coordinateMap_id] at he
  have hq : Function.Injective (FiniteEtale.FiniteCommGroupScheme.coordinateMap (G.inclusion n)) := by
    intro x y hxy
    have h := congrArg (FiniteEtale.FiniteCommGroupScheme.coordinateMap r) hxy
    change ((FiniteEtale.FiniteCommGroupScheme.coordinateMap r).comp
      (FiniteEtale.FiniteCommGroupScheme.coordinateMap (G.inclusion n))) x =
      ((FiniteEtale.FiniteCommGroupScheme.coordinateMap r).comp
        (FiniteEtale.FiniteCommGroupScheme.coordinateMap (G.inclusion n))) y at h
    simpa only [he, AlgHom.id_apply] using h
  have hd := LinearMap.finrank_le_finrank_of_injective
    (f := (FiniteEtale.FiniteCommGroupScheme.coordinateMap (G.inclusion n)).toLinearMap) hq
  rw [G.rank, G.rank, Nat.mul_one, Nat.mul_one] at hd
  exact (Nat.not_le_of_gt
    (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (Nat.lt_succ_self n))) hd

end

end OAI.AlgebraicGeometry.GroupSchemes
