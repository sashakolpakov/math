import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDivision
import Mathlib.GroupTheory.FiniteAbelian.Basic

/-! # Lattice Congruence -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.LatticeCongruence

noncomputable section

/-! The principal congruence kernel of an action on a finitely
generated integral lattice has finite index, at the specified level. -/

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDivision.TorusTorsion

variable {G L : Type*} [Group G] [AddCommGroup L]

def latticeModNAction (N : ℕ) (ρ : G →* (L ≃ₗ[ℤ] L)) :
    G →* Equiv.Perm (L ⧸ AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDivision.TorusTorsion.multipleSubgroup L N) where
  toFun g := (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDivision.TorusTorsion.modNEquiv N (ρ g).toAddEquiv).toEquiv
  map_one' := by
    apply Equiv.ext
    intro x
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
    change QuotientAddGroup.mk (ρ 1 v) = QuotientAddGroup.mk v
    rw [map_one]
    rfl
  map_mul' g h := by
    apply Equiv.ext
    intro x
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
    change QuotientAddGroup.mk (ρ (g * h) v) = QuotientAddGroup.mk (ρ g (ρ h v))
    rw [map_mul]
    rfl

theorem latticeModNAction_ker (N : ℕ) (ρ : G →* (L ≃ₗ[ℤ] L)) (g : G) :
    g ∈ (latticeModNAction N ρ).ker ↔ ∀ x : L, ∃ y : L, ρ g x - x = N • y := by
  constructor
  · intro h x
    have he := Equiv.congr_fun h (QuotientAddGroup.mk x)
    have hm : ρ g x - x ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDivision.TorusTorsion.multipleSubgroup L N := QuotientAddGroup.eq_iff_sub_mem.mp he
    obtain ⟨y, hy⟩ := hm
    exact ⟨y, hy.symm⟩
  · intro h
    apply Equiv.ext
    intro x
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    obtain ⟨w, hw⟩ := h v
    exact ⟨w, hw.symm⟩

theorem latticeModN_finite [AddGroup.FG L] (N : ℕ) (hN : N ≠ 0) :
    Finite (L ⧸ AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDivision.TorusTorsion.multipleSubgroup L N) := by
  let : (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDivision.TorusTorsion.multipleSubgroup L N).FiniteIndex :=
    AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg L hN
  exact AddSubgroup.finite_quotient_of_finiteIndex

theorem latticeModNAction_finiteIndex [AddGroup.FG L]
    (N : ℕ) (hN : N ≠ 0) (ρ : G →* (L ≃ₗ[ℤ] L)) : (latticeModNAction N ρ).ker.FiniteIndex := by
  let : Finite (L ⧸ AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticeDivision.TorusTorsion.multipleSubgroup L N) := latticeModN_finite N hN
  exact Subgroup.finiteIndex_ker _

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.LatticeCongruence
