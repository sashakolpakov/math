import OAI.AlgebraicGeometry.FormalGeometry.Completion.GlobalSectionGeneration
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Closed Section Generation -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! Generation by global sections descends from the direct image along
a closed immersion, using faithfulness of the actual module direct image. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

universe u

theorem ClosedSectionGeneration.Construction.modulePushforward_map_injective_of_isInducing
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Topology.IsInducing f)
    {M N : X.Modules} : Function.Injective ((Scheme.Modules.pushforward f).map (X := M) (Y := N)) := by
  intro a b hab
  apply Scheme.Modules.hom_ext
  intro U
  obtain ⟨V, hV, he⟩ := hf.isOpen_iff.mp U.isOpen
  have he' : f ⁻¹ᵁ (⟨V, hV⟩ : Y.Opens) = U := SetLike.coe_injective he
  have hh := congrArg (fun t => t.app (⟨V, hV⟩ : Y.Opens)) hab
  exact he' ▸ (show a.app (f ⁻¹ᵁ (⟨V, hV⟩ : Y.Opens)) =
    b.app (f ⁻¹ᵁ (⟨V, hV⟩ : Y.Opens)) from hh)

theorem GlobalSectionGeneration.Construction.SectionsDetectMaps.of_pushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : Topology.IsInducing f)
    (M : X.Modules) (hM : GlobalSectionGeneration.Construction.SectionsDetectMaps ((Scheme.Modules.pushforward f).obj M)) :
    GlobalSectionGeneration.Construction.SectionsDetectMaps M := by
  intro N a ha
  apply ClosedSectionGeneration.Construction.modulePushforward_map_injective_of_isInducing f hf
  rw [Functor.map_zero]
  apply hM ((Scheme.Modules.pushforward f).obj N) ((Scheme.Modules.pushforward f).map a)
  simpa only [Scheme.Modules.pushforward_map_app, Scheme.Hom.preimage_top] using ha

theorem GlobalSectionGeneration.Construction.SectionsDetectMaps.of_closed_pushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (M : X.Modules) (hM : GlobalSectionGeneration.Construction.SectionsDetectMaps ((Scheme.Modules.pushforward f).obj M)) :
    GlobalSectionGeneration.Construction.SectionsDetectMaps M :=
  hM.of_pushforward f f.isClosedEmbedding.isEmbedding.isInducing M

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
