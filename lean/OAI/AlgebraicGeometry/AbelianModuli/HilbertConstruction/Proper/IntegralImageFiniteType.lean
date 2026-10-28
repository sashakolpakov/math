import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralRestrictedImageFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FromAffineSectionNeighborhoods

/-! # Integral Image Finite Type -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralImageFiniteType

noncomputable section

/-! A proper surjective map from an integral scheme has finite-type line-bundle direct images over a locally Noetherian base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.TopologicalSpace

universe u

theorem proper_surjective_integral_lineBundle_directImage_finiteType
    {X S : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] [Surjective f] (L : Line.Bundles.LineBundle X) :
    ((pushforward f).obj L.sheaf).IsFiniteType := by
  have : ((pushforward f).obj L.sheaf).IsQuasicoherent :=
    LineBundleImage.proper_lineBundle_directImage_quasicoherent f L
  apply Finite.FromAffineSectionNeighborhoods.module_finiteType_of_affine_section_neighborhoods
  intro y
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, _⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  obtain ⟨x, hx⟩ := f.surjective y
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨x, by
    change f x ∈ U
    rw [hx]
    exact hyU⟩⟩
  exact ⟨U, hyU, hU, IntegralRestrictedImageFiniteness.proper_integral_restricted_directImage_sections_finite f L U hU⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.IntegralImageFiniteType
