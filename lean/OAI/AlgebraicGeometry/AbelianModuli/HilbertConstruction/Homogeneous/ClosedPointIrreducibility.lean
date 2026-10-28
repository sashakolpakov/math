import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Connected.Clopen

/-! # Closed Point Irreducibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ClosedPointIrreducibility

noncomputable section

/-! A connected Noetherian Jacobson space with a transitive homeomorphism
action on its closed points is irreducible. This applies to rational translations. -/
open _root_.TopologicalSpace
variable {X : Type*} [TopologicalSpace X]

theorem irreducibleSpace_of_connected_irreducible_open_cover [ConnectedSpace X]
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsIrreducible U) :
    IrreducibleSpace X := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let C := irreducibleComponent x
  have hC : C ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hopen : IsOpen C := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨U, hU, hyU, hirr⟩ := h y
    have hsub : C ⊆ closure U :=
      (subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.2 hU ⟨y, hy, hyU⟩).trans
        (closure_mono Set.inter_subset_right)
    have hUC : U ⊆ C := subset_closure.trans (hC.2 hirr.closure hsub)
    exact Filter.mem_of_superset (hU.mem_nhds hyU) hUC
  have he : C = Set.univ := IsClopen.eq_univ
    ⟨isClosed_of_mem_irreducibleComponents C hC, hopen⟩ hC.1.1
  apply (irreducibleSpace_def X).mpr
  simpa only [he, Set.top_eq_univ] using hC.1

theorem irreducible_open_cover_of_closedPoints [JacobsonSpace X]
    (h : ∀ x : X, IsClosed {x} → ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsIrreducible U) :
    ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsIrreducible U := by
  let V : Set X := ⋃₀ {U : Set X | IsOpen U ∧ IsIrreducible U}
  have hV : IsOpen V := isOpen_sUnion (fun U hU => hU.1)
  have htop : V = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_contra hx
    obtain ⟨y, hy, hcy⟩ := nonempty_inter_closedPoints
      (show (Vᶜ : Set X).Nonempty from ⟨x, hx⟩) hV.isClosed_compl.isLocallyClosed
    obtain ⟨U, hU, hyU, hirr⟩ := h y hcy
    exact hy (Set.mem_sUnion_of_mem hyU ⟨hU, hirr⟩)
  intro x
  have hx : x ∈ V := htop.symm ▸ Set.mem_univ x
  obtain ⟨U, hU, hxU⟩ := Set.mem_sUnion.mp hx
  exact ⟨U, hU.1, hxU, hU.2⟩

theorem irreducibleSpace_of_homogeneous_closedPoints
    [ConnectedSpace X] [NoetherianSpace X] [JacobsonSpace X]
    (h : ∀ x y : X, IsClosed {x} → IsClosed {y} → ∃ e : X ≃ₜ X, e x = y) :
    IrreducibleSpace X := by
  let x : X := Classical.choice (inferInstance : Nonempty X)
  let U : Set X := (⋃₀ (irreducibleComponents X \ {irreducibleComponent x}))ᶜ
  have hU : IsOpen U := by
    rw [isOpen_compl_iff, Set.sUnion_eq_biUnion]
    exact NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      (fun C hC => isClosed_of_mem_irreducibleComponents C hC.1)
  have hcl : closure U = irreducibleComponent x :=
    closure_sUnion_irreducibleComponents_sdiff_singleton
      NoetherianSpace.finite_irreducibleComponents _ (irreducibleComponent_mem_irreducibleComponents x)
  have hirr : IsIrreducible U := isIrreducible_iff_closure.mp
    (hcl.symm ▸ (isIrreducible_irreducibleComponent (x := x)))
  obtain ⟨a, haU, hca⟩ := nonempty_inter_closedPoints hirr.1 hU.isLocallyClosed
  apply irreducibleSpace_of_connected_irreducible_open_cover
  apply irreducible_open_cover_of_closedPoints
  intro b hcb
  obtain ⟨e, he⟩ := h a b hca hcb
  exact ⟨e '' U, e.isOpenMap U hU, ⟨a, haU, he⟩, hirr.image e e.continuous.continuousOn⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ClosedPointIrreducibility
