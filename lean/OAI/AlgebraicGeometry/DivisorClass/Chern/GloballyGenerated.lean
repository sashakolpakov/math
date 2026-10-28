import OAI.AlgebraicGeometry.DivisorClass.Chern.Generating
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Map
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Fin

/-! # Globally Generated -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GloballyGenerated

noncomputable section

/-! A globally generated original holomorphic line bundle has the negative of its original Chern class realized by an actual algebraic line bundle. -/

open _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem exists_globallyGenerated_algebraicChern (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (hu : HolomorphicSection.Fin.holomorphicLineGloballyGenerated u) :
    ∃ L : Line.Bundles.AlgebraicLineBundle V.presentation,
      First.firstChernClassQ V.presentation L = -Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace u := by
  obtain ⟨n, s, hs⟩ := HolomorphicSection.Fin.exists_fin_holomorphic_generators u hu
  obtain ⟨g, hg⟩ := HolomorphicSection.Map.exists_holomorphicSection_algebraic_map V u s hs
  exact ⟨GeneratingLineBundle.generatingAlgebraicLineBundle V.presentation g,
    Generating.generatingAlgebraicLineBundle_firstChern V u s hs g hg⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GloballyGenerated
