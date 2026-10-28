import OAI.AlgebraicGeometry.Comparison.Betti.Projective.Concrete
import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ComponentPresentations
import OAI.AlgebraicGeometry.Comparison.Betti.Component

/-! # Smooth Isomorphism -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.SmoothIsomorphism

noncomputable section

/-! The original smooth de Rham–Betti comparison is an isomorphism for every projective presentation, including disconnected and empty schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] Betti.Smooth.ReferenceCongruence.componentMetrizable

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

theorem projectivePresentation_smoothDeRhamBettiMap_isIso
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X.left X.hom) (n : ℕ) : IsIso (Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap X n) := by
  apply Component.smoothDeRhamBettiMap_isIso_of_components X n
  intro C
  exact Concrete.projectivePresentation_algebraicDeRhamBettiMap_isIso (Betti.Smooth.Components.componentOver X C)
    (ComponentPresentations.Components.componentProjectivePresentation X P C) n

local instance projectiveComparisonToOverSmooth (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) : Smooth P.toOver.hom :=
  P.smooth

local instance projectiveComparisonToOverProper (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) : IsProper P.toOver.hom :=
  P.projective.isProper

theorem smoothProjective_smoothDeRhamBettiMap_isIso (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (n : ℕ) :
    IsIso (Betti.Smooth.ReferenceCongruence.smoothDeRhamBettiMap P.toOver n) :=
  projectivePresentation_smoothDeRhamBettiMap_isIso P.toOver P.projective n

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.SmoothIsomorphism
