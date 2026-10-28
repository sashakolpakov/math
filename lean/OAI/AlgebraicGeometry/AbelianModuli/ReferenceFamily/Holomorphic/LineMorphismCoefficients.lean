import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineMorphismHolomorphicCoefficients

/-! # Line Morphism Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.LineMorphismCoefficients

noncomputable section

/-! Holomorphic morphism coefficients are literal holomorphic functions
in every pair of actual algebraic line frames, with their frame-change
identity. Actual algebraic sheaf maps supply these coefficients. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

structure HolomorphicLineMorphismCoefficients (L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier) where
  coefficient (r : LineFrameAtlas.LocalLineFrame L.sheaf) (s : LineFrameAtlas.LocalLineFrame K.sheaf) :
    DivisorClass.Chern.Holomorphic.Exponential.HolomorphicFunction (E := V.analyticModel)
      (M := (AnalyticFrameTransitions.frameAnalyticOpen V.presentation r ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s : Opens V.analyticSpace))
  frame_change (r₀ r₁ : LineFrameAtlas.LocalLineFrame L.sheaf) (s₀ s₁ : LineFrameAtlas.LocalLineFrame K.sheaf) (x : V.analyticSpace)
      (h₀ : x ∈ AnalyticFrameTransitions.frameAnalyticOpen V.presentation r₀ ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s₀)
      (h₁ : x ∈ AnalyticFrameTransitions.frameAnalyticOpen V.presentation r₁ ⊓ AnalyticFrameTransitions.frameAnalyticOpen V.presentation s₁) :
    AnalyticFrameTransitions.framePointTransition V.presentation r₀ r₁ x h₀.1 h₁.1 * coefficient r₀ s₀ ⟨x, h₀⟩ =
      coefficient r₁ s₁ ⟨x, h₁⟩ * AnalyticFrameTransitions.framePointTransition V.presentation s₀ s₁ x h₀.2 h₁.2

@[ext]
theorem HolomorphicLineMorphismCoefficients.ext {L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier}
    {D E : HolomorphicLineMorphismCoefficients V L K}
    (h : ∀ r s, D.coefficient r s = E.coefficient r s) : D = E := by
  cases D
  cases E
  congr
  funext r s
  exact h r s

def holomorphicLineMorphismCoefficientsOfAlgebraic (L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier) (f : L.sheaf ⟶ K.sheaf) :
    HolomorphicLineMorphismCoefficients V L K where
  coefficient := LineMorphismHolomorphicCoefficients.lineMorphismHolomorphicCoefficient V f
  frame_change := LineMorphismHolomorphicCoefficients.lineMorphismHolomorphicCoefficient_frame_change V f

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Holomorphic.LineMorphismCoefficients
