import OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedSectionGeneration

/-! # Closed Morphism Reflection -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedMorphismReflection.Construction

noncomputable section

/-! A module morphism is surjective if its actual direct image along
an inducing scheme morphism is surjective. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

theorem moduleMap_epi_of_pushforward_epi {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : Topology.IsInducing f) {M N : X.Modules} (a : M ⟶ N)
    [Epi ((Scheme.Modules.pushforward f).map a)] : Epi a := by
  constructor
  intro Z g h hgh
  apply ClosedSectionGeneration.Construction.modulePushforward_map_injective_of_isInducing f hf
  apply (cancel_epi ((Scheme.Modules.pushforward f).map a)).mp
  rw [← (Scheme.Modules.pushforward f).map_comp, ← (Scheme.Modules.pushforward f).map_comp, hgh]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.ClosedMorphismReflection.Construction
