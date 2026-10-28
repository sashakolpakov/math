import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameEvaluation
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RegularEvaluation

/-! # Line Morphism Holomorphic Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineMorphismHolomorphicCoefficients

noncomputable section

/-! Actual regular coefficients of a sheaf morphism give native
holomorphic coefficients, with the literal frame-change law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RegularEvaluation

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {M N : V.carrier.Modules}

def lineMorphismHolomorphicCoefficient (f : M ⟶ N) (r : LineFrameAtlas.LocalLineFrame M) (s : LineFrameAtlas.LocalLineFrame N) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel)
      (M := (AnalyticFrameTransitions.frameAnalyticOpen V.presentation r ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s : Opens V.analyticSpace)) :=
  DivisorClass.Chern.Holomorphic.RegularEvaluation.regularSectionHolomorphicEvaluation V (r.domain ⊓ s.domain)
    (LineFrameAtlas.lineMorphismCoefficient f r s (r.domain ⊓ s.domain) inf_le_left inf_le_right)

theorem lineMorphismHolomorphicCoefficient_value (f : M ⟶ N) (r : LineFrameAtlas.LocalLineFrame M) (s : LineFrameAtlas.LocalLineFrame N)
    (x : V.analyticSpace) (hx : x ∈ AnalyticFrameTransitions.frameAnalyticOpen V.presentation r ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s) :
    lineMorphismHolomorphicCoefficient V f r s ⟨x, hx⟩ =
      RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left (r.domain ⊓ s.domain) hx
        (LineFrameAtlas.lineMorphismCoefficient f r s (r.domain ⊓ s.domain) inf_le_left inf_le_right) :=
  Intrinsic.FrameEvaluation.sectionEvaluationOn_native V.presentation (r.domain ⊓ s.domain) _ ⟨x, hx⟩

theorem lineMorphismCoefficient_value_restrict (f : M ⟶ N) (r : LineFrameAtlas.LocalLineFrame M) (s : LineFrameAtlas.LocalLineFrame N)
    {U W : V.carrier.Opens} (h : W ≤ U) (hr : U ≤ r.domain) (hs : U ≤ s.domain)
    (x : V.analyticSpace) (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W) :
    RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left W hx (LineFrameAtlas.lineMorphismCoefficient f r s W (h.trans hr) (h.trans hs)) =
      RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left U (h hx) (LineFrameAtlas.lineMorphismCoefficient f r s U hr hs) :=
  (congrArg (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left W hx) (LineFrameAtlas.lineMorphismCoefficient_restrict f r s h hr hs)).trans
    (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_restrict x.left U W h hx _)

theorem lineMorphismHolomorphicCoefficient_value_on_open (f : M ⟶ N)
    (r : LineFrameAtlas.LocalLineFrame M) (s : LineFrameAtlas.LocalLineFrame N) (U : V.carrier.Opens)
    (hr : U ≤ r.domain) (hs : U ≤ s.domain) (x : V.analyticSpace)
    (hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ U) :
    lineMorphismHolomorphicCoefficient V f r s ⟨x, hr hx, hs hx⟩ =
      RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left U hx (LineFrameAtlas.lineMorphismCoefficient f r s U hr hs) :=
  (lineMorphismHolomorphicCoefficient_value V f r s x ⟨hr hx, hs hx⟩).trans
    (lineMorphismCoefficient_value_restrict V f r s (le_inf hr hs) inf_le_left inf_le_right x hx).symm

theorem lineMorphismHolomorphicCoefficient_frame_change (f : M ⟶ N)
    (r₀ r₁ : LineFrameAtlas.LocalLineFrame M) (s₀ s₁ : LineFrameAtlas.LocalLineFrame N) (x : V.analyticSpace)
    (h₀ : x ∈ AnalyticFrameTransitions.frameAnalyticOpen V.presentation r₀ ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s₀)
    (h₁ : x ∈ AnalyticFrameTransitions.frameAnalyticOpen V.presentation r₁ ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s₁) :
    AnalyticFrameTransitions.framePointTransition V.presentation r₀ r₁ x h₀.1 h₁.1 *
      lineMorphismHolomorphicCoefficient V f r₀ s₀ ⟨x, h₀⟩ =
    lineMorphismHolomorphicCoefficient V f r₁ s₁ ⟨x, h₁⟩ *
      AnalyticFrameTransitions.framePointTransition V.presentation s₀ s₁ x h₀.2 h₁.2 := by
  let W := (r₀.domain ⊓ s₀.domain) ⊓ (r₁.domain ⊓ s₁.domain)
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ W := ⟨h₀, h₁⟩
  have hr₀ : W ≤ r₀.domain := inf_le_left.trans inf_le_left
  have hr₁ : W ≤ r₁.domain := inf_le_right.trans inf_le_left
  have hs₀ : W ≤ s₀.domain := inf_le_left.trans inf_le_right
  have hs₁ : W ≤ s₁.domain := inf_le_right.trans inf_le_right
  have hr := (AnalyticFrameTransitions.framePointTransition_restrict V.presentation r₀ r₁ W hr₀ hr₁ ⟨x, hx⟩).trans
    (Intrinsic.FrameEvaluation.sectionEvaluationOn_native V.presentation W (r₀.transition r₁ W hr₀ hr₁) ⟨x, hx⟩)
  have hs := (AnalyticFrameTransitions.framePointTransition_restrict V.presentation s₀ s₁ W hs₀ hs₁ ⟨x, hx⟩).trans
    (Intrinsic.FrameEvaluation.sectionEvaluationOn_native V.presentation W (s₀.transition s₁ W hs₀ hs₁) ⟨x, hx⟩)
  have hc₀ := lineMorphismCoefficient_value_restrict V f r₀ s₀
    (show W ≤ r₀.domain ⊓ s₀.domain from inf_le_left) inf_le_left inf_le_right x hx
  have hc₁ := lineMorphismCoefficient_value_restrict V f r₁ s₁
    (show W ≤ r₁.domain ⊓ s₁.domain from inf_le_right) inf_le_left inf_le_right x hx
  have h := congrArg (RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left W hx)
    (LineFrameAtlas.lineMorphismCoefficient_frame_change f r₀ r₁ s₀ s₁ W hr₀ hr₁ hs₀ hs₁)
  erw [map_mul, map_mul, ← hr, ← hs, hc₀, hc₁,
    ← lineMorphismHolomorphicCoefficient_value V f r₀ s₀ x h₀,
    ← lineMorphismHolomorphicCoefficient_value V f r₁ s₁ x h₁] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineMorphismHolomorphicCoefficients
