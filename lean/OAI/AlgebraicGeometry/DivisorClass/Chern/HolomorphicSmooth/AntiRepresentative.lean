import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiOneSourcePair

/-! # Anti Representative -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.AntiRepresentative

noncomputable section

/-! A genuine smooth representative of an actual antiholomorphic L² element is itself antiholomorphic. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicMetric_smooth_representative_anti (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (v : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h) (b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1)
    (hb : Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 b = v.val) :
    ∃ c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1, Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h c = v := by
  have hmem : Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 b ∈ h.antiOneL2Submodule V := hb.symm ▸ v.property
  change HolomorphicMetric.Equivalence.holomorphicMetricOriginalL2Equiv V h 1 (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 b) ∈
    Holomorphic.AntiOneHilbert.holomorphicAntiOneL2Submodule V u at hmem
  rw [HolomorphicMetric.Equivalence.holomorphicMetricOriginalL2Equiv_inclusion] at hmem
  have hfix := (Holomorphic.AntiOneHilbert.holomorphicAntiOneL2_mem V u _).mp hmem
  have hpart : Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I b = b :=
    Holomorphic.FormCompletion.holomorphicFormL2Inclusion_injective V u 1 ((Holomorphic.AntiOneHilbert.holomorphicL2OnePart_inclusion V u b).symm.trans hfix)
  have hanti : b ∈ HolomorphicLine.AntiForms.holomorphicLineAntiFormSubmodule u ⊤ 1 :=
    hpart ▸ Holomorphic.OneFormProjection.holomorphicLineOnePart_anti u ⊤ b
  refine ⟨⟨b, hanti⟩, Subtype.ext ?_⟩
  exact (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_val V h ⟨b, hanti⟩).trans hb

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.AntiRepresentative
