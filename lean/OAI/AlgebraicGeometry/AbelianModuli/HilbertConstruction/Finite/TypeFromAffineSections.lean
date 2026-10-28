import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FromAffineSectionNeighborhoods
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RestrictionSectionFiniteness

/-! # Type From Affine Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeFromAffineSections

noncomputable section

/-! Finite modules of sections on affine opens characterize finite type for quasicoherent sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.TopologicalSpace

universe u

theorem module_finiteType_of_affine_sections_finite {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent]
    (hfinite : ∀ U : X.affineOpens, Module.Finite Γ(X, U.1) Γ(M, U.1)) :
    M.IsFiniteType := by
  apply FromAffineSectionNeighborhoods.module_finiteType_of_affine_section_neighborhoods
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Module.Finite Γ(X, U) Γ(M, U) := hfinite ⟨U, hU⟩
  exact ⟨U, hxU, hU, RestrictionSectionFiniteness.module_restrict_sections_finite_of_sections_finite M U⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.TypeFromAffineSections
