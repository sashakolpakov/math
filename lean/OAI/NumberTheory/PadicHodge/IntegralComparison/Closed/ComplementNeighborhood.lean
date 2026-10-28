import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Complement Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.ComplementNeighborhood

noncomputable section

/-! Outside the actual image of a closed immersion, affine subopens have
the unit defining ideal. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem kernel_eq_top_of_preimage_bot {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (hV : f ⁻¹ᵁ V = ⊥) : RingHom.ker (f.app V).hom = ⊤ := by
  have : Subsingleton Γ(X, f ⁻¹ᵁ V) := by rw [hV]; infer_instance
  apply top_unique
  intro a _
  exact Subsingleton.elim _ _

theorem exists_affine {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (U : Y.Opens) (y : Y) (hyU : y ∈ U) (hy : y ∉ Set.range f) :
    ∃ (V : Y.Opens) (_ : IsAffineOpen V), V ≤ U ∧ y ∈ V ∧ RingHom.ker (f.app V).hom = ⊤ := by
  let W : Y.Opens := ⟨(Set.range f)ᶜ, f.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hmem : y ∈ U ⊓ W := ⟨hyU, hy⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hmem (U ⊓ W).isOpen
  refine ⟨V, hV, fun z hz => (hVW hz).1, hyV, kernel_eq_top_of_preimage_bot f V ?_⟩
  apply le_bot_iff.mp
  intro z hz
  exact False.elim ((hVW hz).2 ⟨z, rfl⟩)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.ComplementNeighborhood
