import OAI.RepresentationTheory.Theta.Geometric.Projective.EtaleCovering
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveComponent

/-! # Disconnected Etale Covering -/

namespace OAI.RepresentationTheory.Theta.Geometric.DisconnectedEtaleCovering

noncomputable section

/-! Finite étale maps from an arbitrary smooth projective source, including
disconnected sources, are actual analytic covering maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem smoothProjectiveFiniteEtale_isLocalHomeomorph
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (Y : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (f : P.toOver ⟶ Y.toOver) [IsFinite f.left] [Etale f.left] :
    IsLocalHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  intro x
  obtain ⟨⟨C, p⟩, hp⟩ := P.componentPointsHomeomorph.surjective x
  let i := P.componentInclusionOver C
  have : IsFinite (i ≫ f).left := inferInstanceAs (IsFinite (i.left ≫ f.left))
  have : Etale (i ≫ f).left := inferInstanceAs (Etale (i.left ≫ f.left))
  have hfi : IsLocalHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) :=
    (Projective.EtaleCovering.projectiveFiniteEtale_isCoveringMap (P.componentVariety C) Y (i ≫ f)).isLocalHomeomorph
  have hi := (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion i).isLocalHomeomorph
  have hl := hfi.isLocalHomeomorphOn.of_comp_right
    (show IsLocalHomeomorphOn (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) Set.univ from hi.isLocalHomeomorphOn)
  exact hl x ⟨p, Set.mem_univ p, hp⟩

theorem smoothProjectiveFiniteEtale_isCoveringMap
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (Y : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (f : P.toOver ⟶ Y.toOver) [IsFinite f.left] [Etale f.left] :
    IsCoveringMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) :=
  AlgebraicGeometry.Cycles.Functoriality.Covering.Construction.covering_of_proper_localHomeomorph _
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map f).isProperMap
    (smoothProjectiveFiniteEtale_isLocalHomeomorph P Y f)

theorem smoothProjectiveFiniteEtale_finite_fiber
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (Y : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (f : P.toOver ⟶ Y.toOver) [IsFinite f.left] [Etale f.left] (y : Y.analyticSpace) :
    ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) ⁻¹' {y}).Finite :=
  AlgebraicGeometry.Cycles.Functoriality.Covering.Construction.finite_fiber_of_proper_localHomeomorph _
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map f).isProperMap
    (smoothProjectiveFiniteEtale_isLocalHomeomorph P Y f) y

end

end OAI.RepresentationTheory.Theta.Geometric.DisconnectedEtaleCovering
