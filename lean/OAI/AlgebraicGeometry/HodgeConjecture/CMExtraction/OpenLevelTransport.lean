import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # Open Level Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OpenLevelTransport.Approximation

/-! Transport open subgroups and a full family of principal containment
bounds through a specified topological group equivalence. -/

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  (e : G ≃ₜ* H) (L : OpenSubgroup G)

def transportOpenLevel : OpenSubgroup H := L.comap e.symm.toMulEquiv.toMonoidHom e.symm.continuous

theorem transportOpenLevel_mem (g : G) : e g ∈ transportOpenLevel e L ↔ g ∈ L := by
  change e.symm (e g) ∈ L ↔ g ∈ L
  rw [e.symm_apply_apply]

theorem transportOpenLevel_principal_depth (S : ℕ → Subgroup H)
    (h : ∃ M : ℕ, 0 < M ∧ ∀ N : ℕ, M ∣ N → S N ≤ (transportOpenLevel e L).toSubgroup) :
    ∃ M : ℕ, 0 < M ∧ ∀ N : ℕ, M ∣ N → ∀ g : G, e g ∈ S N → g ∈ L := by
  obtain ⟨M, hM, hsmall⟩ := h
  exact ⟨M, hM, fun N hN g hg => (transportOpenLevel_mem e L g).mp (hsmall N hN hg)⟩

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OpenLevelTransport.Approximation
