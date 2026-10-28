import OAI.AlgebraicGeometry.DivisorClass.Chern.ExtendedProjective
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicChernSpan

/-! # Component Projective Span -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ComponentProjectiveSpan

noncomputable section

section

/-! Extension of a component's projective Chern span lies in the original presentation's projective Chern span. -/

open _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem componentProjectiveSpan_extension_mem (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (C : irreducibleComponents P.carrier) (a : (P.componentVariety C).rationalCohomology 2)
    (ha : a ∈ HolomorphicChernSpan.projectiveChernSpan (P.componentVariety C).presentation) :
    ComponentCohomologyExtension.componentCohomologyExtension P C a ∈ HolomorphicChernSpan.projectiveChernSpan P := by
  have h : HolomorphicChernSpan.projectiveChernSpan (P.componentVariety C).presentation ≤
      (HolomorphicChernSpan.projectiveChernSpan P).comap (ComponentCohomologyExtension.componentCohomologyExtension P C) := by
    apply Submodule.span_le.mpr
    rintro c ⟨n, g, rfl⟩
    change ComponentCohomologyExtension.componentCohomologyExtension P C
      (First.firstChernClassQ (P.componentVariety C).presentation
        (GeneratingLineBundle.generatingAlgebraicLineBundle (P.componentVariety C).presentation g)) ∈ HolomorphicChernSpan.projectiveChernSpan P
    rw [← ExtendedProjective.extendedProjectiveChernClass P C g]
    exact Submodule.subset_span ⟨n, ExtendComponentProjectiveMap.extendComponentProjectiveMap P C g, rfl⟩
  exact h ha

end

/-! The unconditional original rational Lefschetz (1,1) theorem, including empty, disconnected, and mixed-dimensional smooth projective presentations. -/

open _root_.CategoryTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem originalPresentation_lefschetz_one_one (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (a : P.rationalCohomology 2) (ha : P.IsRationalHodgeClass 1 a) :
    a ∈ Submodule.span ℚ (Set.range (First.firstChernClassQ P)) := by
  classical
  let : Fintype (irreducibleComponents P.carrier) := Fintype.ofFinite _
  apply HolomorphicChernSpan.projectiveChernSpan_le_algebraicChernSpan P
  rw [← ComponentCohomologyExtension.componentCohomologyExtension_sum P a]
  apply (HolomorphicChernSpan.projectiveChernSpan P).sum_mem
  intro C _
  apply componentProjectiveSpan_extension_mem
  exact HolomorphicChernSpan.integralVariety_lefschetz_projectiveSpan (P.componentVariety C)
    (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) 2 a C) ((P.isRationalHodgeClass_iff_components 1 a).mp ha C)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ComponentProjectiveSpan
