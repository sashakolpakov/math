import OAI.AlgebraicGeometry.DivisorClass.Chern.GloballyGenerated
import OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.TwistGlobalGeneration
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Additive
import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.SpanDivision
import OAI.AlgebraicGeometry.DivisorClass.Chern.ReferenceHodgeHolomorphicBundles

/-! # Holomorphic Chern Span -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicChernSpan

noncomputable section

section

/-! Global generation and the actual algebraic bundle construction place every original holomorphic Chern class in the original algebraic rational span. -/

open _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

local instance algebraicSpanLocallyContractible (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    StronglyLocallyContractibleSpace V.analyticSpace :=
  AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace V.analyticModel V.analyticSpace

abbrev algebraicChernSpan (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :=
  Submodule.span ℚ (Set.range (First.firstChernClassQ P))

theorem holomorphicChern_mem_algebraicSpan_of_globallyGenerated (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (hu : HolomorphicSection.Fin.holomorphicLineGloballyGenerated u) :
    Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace u ∈ algebraicChernSpan V.presentation := by
  obtain ⟨L, hL⟩ := GloballyGenerated.exists_globallyGenerated_algebraicChern V u hu
  have h : First.firstChernClassQ V.presentation L ∈ algebraicChernSpan V.presentation :=
    Submodule.subset_span ⟨L, rfl⟩
  rw [hL] at h
  simpa only [neg_neg] using (algebraicChernSpan V.presentation).neg_mem h

theorem fubiniStudyTwistChern_mem_algebraicSpan (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace (FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) ∈
      algebraicChernSpan V.presentation := by
  obtain ⟨N, hN, hG⟩ := FubiniStudyGeneratedMultiple.exists_fubiniStudyTwist_globally_generated_multiple V
  have h := holomorphicChern_mem_algebraicSpan_of_globallyGenerated V (N • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) hG
  rw [Holomorphic.Additive.holomorphicFirstChernClassQ_nsmul] at h
  exact Rational.SpanDivision.rationalSubmodule_mem_of_positive_nsmul (algebraicChernSpan V.presentation) _ N hN h

theorem holomorphicChern_mem_algebraicSpan (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) :
    Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace u ∈ algebraicChernSpan V.presentation := by
  obtain ⟨N, _, hG⟩ := Positive.TwistGlobalGeneration.exists_positiveHolomorphicTwist_globally_generated V (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u)
  have h := holomorphicChern_mem_algebraicSpan_of_globallyGenerated V (u + N • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) hG
  have ha := (Holomorphic.Additive.holomorphicFirstChernClassQHom V.analyticModel V.analyticSpace).map_add u
    (N • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V)
  change Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace (u + N • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) =
    Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace u +
      Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace (N • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) at ha
  rw [Holomorphic.Additive.holomorphicFirstChernClassQ_nsmul V.analyticModel V.analyticSpace N (FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V)] at ha
  have h' : Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace u +
      N • Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace (FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) ∈
      algebraicChernSpan V.presentation := ha ▸ h
  have hb := (algebraicChernSpan V.presentation).nsmul_mem
    (fubiniStudyTwistChern_mem_algebraicSpan V) N
  simpa only [add_sub_cancel_right] using (algebraicChernSpan V.presentation).sub_mem h' hb

end

section

/-! The unconditional original rational Lefschetz (1,1) span statement on an actual integral projective variety. -/

open _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem integralVariety_lefschetz_one_one (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : V.rationalCohomology 2) (ha : V.IsRationalHodgeClass 1 a) :
    a ∈ Submodule.span ℚ (Set.range (First.firstChernClassQ V.presentation)) := by
  have h := holomorphicChern_mem_algebraicSpan V (ReferenceHodgeHolomorphicBundles.originalHodgeHolomorphicUnitClass V a ha)
  rw [ReferenceHodgeHolomorphicBundles.originalHodgeHolomorphicUnitClass_chern] at h
  exact Rational.SpanDivision.rationalSubmodule_mem_of_positive_nsmul (algebraicChernSpan V.presentation) a
    (ReferenceHodgeHolomorphicBundles.originalHodgeIntegralMultiple V a ha) (ReferenceHodgeHolomorphicBundles.originalHodgeIntegralMultiple_pos V a ha) h

theorem originalPresentationHodge_component_mem_algebraicSpan (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (a : P.rationalCohomology 2) (ha : P.IsRationalHodgeClass 1 a)
    (C : irreducibleComponents P.carrier) :
    P.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2 a C ∈
      Submodule.span ℚ (Set.range (First.firstChernClassQ (P.componentVariety C).presentation)) :=
  integralVariety_lefschetz_one_one (P.componentVariety C)
    (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2 a C) ((P.isRationalHodgeClass_iff_components 1 a).mp ha C)

end

/-! The stronger span generated by actual projective morphisms, for subsequent component globalization. -/

open _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

local instance projectiveSpanLocallyContractible (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    StronglyLocallyContractibleSpace V.analyticSpace :=
  AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace V.analyticModel V.analyticSpace

def projectiveChernClasses (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) : Set (P.rationalCohomology 2) :=
  {c | ∃ n : ℕ, ∃ g : P.toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver,
    First.firstChernClassQ P (GeneratingLineBundle.generatingAlgebraicLineBundle P g) = c}

abbrev projectiveChernSpan (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) := Submodule.span ℚ (projectiveChernClasses P)

theorem projectiveChernSpan_le_algebraicChernSpan (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    projectiveChernSpan P ≤ algebraicChernSpan P := by
  apply Submodule.span_le.mpr
  rintro c ⟨n, g, rfl⟩
  exact Submodule.subset_span ⟨GeneratingLineBundle.generatingAlgebraicLineBundle P g, rfl⟩

theorem holomorphicChern_mem_of_generated_mem (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (S : Submodule ℚ (V.rationalCohomology 2))
    (hS : ∀ u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace,
      HolomorphicSection.Fin.holomorphicLineGloballyGenerated u → Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace u ∈ S)
    (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) :
    Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace u ∈ S := by
  obtain ⟨m, hm, hbase⟩ := FubiniStudyGeneratedMultiple.exists_fubiniStudyTwist_globally_generated_multiple V
  have hb := hS (m • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) hbase
  rw [Holomorphic.Additive.holomorphicFirstChernClassQ_nsmul V.analyticModel V.analyticSpace m (FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V)] at hb
  have hbaseChern := Rational.SpanDivision.rationalSubmodule_mem_of_positive_nsmul S _ m hm hb
  obtain ⟨N, _, hG⟩ := Positive.TwistGlobalGeneration.exists_positiveHolomorphicTwist_globally_generated V (HolomorphicMetric.Data.holomorphicLineCanonicalMetric u)
  have h := hS (u + N • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) hG
  have ha := (Holomorphic.Additive.holomorphicFirstChernClassQHom V.analyticModel V.analyticSpace).map_add u
    (N • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V)
  change Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace (u + N • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) =
    Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace u +
      Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace (N • FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) at ha
  rw [Holomorphic.Additive.holomorphicFirstChernClassQ_nsmul V.analyticModel V.analyticSpace N (FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V)] at ha
  have h' : Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace u +
      N • Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace (FubiniStudyHolomorphic.fubiniStudyTwistUnitClass V) ∈ S := ha ▸ h
  simpa only [add_sub_cancel_right] using S.sub_mem h' (S.nsmul_mem hbaseChern N)

theorem holomorphicChern_mem_projectiveSpan (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) :
    Holomorphic.Singular.holomorphicFirstChernClassQ V.analyticModel V.analyticSpace u ∈ projectiveChernSpan V.presentation := by
  apply holomorphicChern_mem_of_generated_mem V (projectiveChernSpan V.presentation) _ u
  intro v hv
  obtain ⟨n, s, hs⟩ := HolomorphicSection.Fin.exists_fin_holomorphic_generators v hv
  obtain ⟨g, hg⟩ := HolomorphicSection.Map.exists_holomorphicSection_algebraic_map V v s hs
  have hc := Generating.generatingAlgebraicLineBundle_firstChern V v s hs g hg
  have hm : First.firstChernClassQ V.presentation (GeneratingLineBundle.generatingAlgebraicLineBundle V.presentation g) ∈
      projectiveChernSpan V.presentation := Submodule.subset_span ⟨n, g, rfl⟩
  rw [hc] at hm
  simpa only [neg_neg] using (projectiveChernSpan V.presentation).neg_mem hm

theorem integralVariety_lefschetz_projectiveSpan (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (a : V.rationalCohomology 2) (ha : V.IsRationalHodgeClass 1 a) : a ∈ projectiveChernSpan V.presentation := by
  have h := holomorphicChern_mem_projectiveSpan V (ReferenceHodgeHolomorphicBundles.originalHodgeHolomorphicUnitClass V a ha)
  rw [ReferenceHodgeHolomorphicBundles.originalHodgeHolomorphicUnitClass_chern] at h
  exact Rational.SpanDivision.rationalSubmodule_mem_of_positive_nsmul (projectiveChernSpan V.presentation) a
    (ReferenceHodgeHolomorphicBundles.originalHodgeIntegralMultiple V a ha) (ReferenceHodgeHolomorphicBundles.originalHodgeIntegralMultiple_pos V a ha) h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicChernSpan
