import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Linear Quotient Homeomorph -/

namespace OAI.RepresentationTheory.Theta.Geometric.LinearQuotientHomeomorph

noncomputable section

/-! An actual continuous real linear equivalence carrying one full
additive lattice onto another induces the corresponding quotient homeomorphism. -/

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (T : V ≃L[ℝ] W) (Λ : AddSubgroup V) (Γ : AddSubgroup W)
    (h : ∀ v, T v ∈ Γ ↔ v ∈ Λ)

def linearQuotientHomeomorph : (V ⧸ Λ) ≃ₜ (W ⧸ Γ) := by
  have he : Λ.map T.toLinearEquiv.toAddEquiv = Γ := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (h v).mpr hv
    · intro hw
      exact ⟨T.symm w, (h (T.symm w)).mp (by simpa only [T.apply_symm_apply] using hw), T.apply_symm_apply w⟩
  let e := QuotientAddGroup.congr Λ Γ T.toLinearEquiv.toAddEquiv he
  have hc : Continuous e :=
    (QuotientAddGroup.isQuotientMap_mk Λ).continuous_iff.mpr
      (QuotientAddGroup.continuous_mk.comp T.continuous)
  have ho : IsOpenMap e :=
    QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap_iff.mpr
      (QuotientAddGroup.isOpenQuotientMap_mk.isOpenMap.comp T.toHomeomorph.isOpenMap)
  exact e.toEquiv.toHomeomorphOfContinuousOpen hc ho

theorem linearQuotientHomeomorph_mk (v : V) :
    linearQuotientHomeomorph T Λ Γ h (QuotientAddGroup.mk v) = QuotientAddGroup.mk (T v) := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.LinearQuotientHomeomorph
