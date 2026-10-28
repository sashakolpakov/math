import OAI.RepresentationTheory.Theta.Geometric.Torus.Manifold

/-! # Ring Action -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus

noncomputable section

/-! Actual holomorphic ring actions on projective period quotients. -/

open scoped _root_.Manifold ContDiff

variable (Φ : Data.CM.ProjectivePeriodData) {R : Type} [Ring R]
  (r : R →+* Module.End ℂ Φ.space)
  (hr : ∀ a v, v ∈ Φ.periodIntegerLattice → r a v ∈ Φ.periodIntegerLattice)

def Data.CM.ProjectivePeriodData.quotientRingAction : R →+* AddMonoid.End Φ.periodTorus where
  toFun a := QuotientAddGroup.map Φ.periodIntegerLattice.toAddSubgroup
    Φ.periodIntegerLattice.toAddSubgroup (r a).toAddMonoidHom (hr a)
  map_zero' := by
    apply AddMonoidHom.ext
    intro z
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
    change QuotientAddGroup.mk (r 0 v) = (0 : Φ.periodTorus)
    rw [map_zero]
    rfl
  map_one' := by
    apply AddMonoidHom.ext
    intro z
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
    change QuotientAddGroup.mk (r 1 v) = QuotientAddGroup.mk v
    rw [map_one]
    rfl
  map_add' := by
    intro a b
    apply AddMonoidHom.ext
    intro z
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
    change QuotientAddGroup.mk (r (a + b) v) =
      QuotientAddGroup.mk (r a v) + QuotientAddGroup.mk (r b v)
    rw [map_add]
    exact QuotientAddGroup.mk_add Φ.periodIntegerLattice.toAddSubgroup (r a v) (r b v)
  map_mul' := by
    intro a b
    apply AddMonoidHom.ext
    intro z
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective z
    change QuotientAddGroup.mk (r (a * b) v) = QuotientAddGroup.mk (r a (r b v))
    rw [map_mul]
    rfl

@[simp] theorem Data.CM.ProjectivePeriodData.quotientRingAction_mk (a : R) (v : Φ.space) :
    Φ.quotientRingAction r hr a (QuotientAddGroup.mk v) = QuotientAddGroup.mk (r a v) := rfl

theorem Data.CM.ProjectivePeriodData.quotientRingAction_contMDiff (a : R) :
    ContMDiff 𝓘(ℂ, Φ.space) 𝓘(ℂ, Φ.space) ∞ (Φ.quotientRingAction r hr a) := by
  apply Φ.contMDiff_of_periodProjection
  exact Φ.periodProjection_contMDiff.comp
    (LinearMap.toContinuousLinearMap (r a)).contDiff.contMDiff

end

end OAI.RepresentationTheory.Theta.Geometric.Torus
