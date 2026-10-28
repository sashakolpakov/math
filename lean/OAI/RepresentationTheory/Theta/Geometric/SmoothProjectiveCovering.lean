import OAI.RepresentationTheory.Theta.Geometric.DisconnectedEtaleCovering
import OAI.RepresentationTheory.Theta.Geometric.Projective.ComponentFactorization

/-! # Smooth Projective Covering -/

namespace OAI.RepresentationTheory.Theta.Geometric.SmoothProjectiveCovering

noncomputable section

/-! Finite étale maps between arbitrary smooth projective schemes are
covering maps on their original complex points. Both may be disconnected. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem integralToProjectiveFiniteEtale_isLocalHomeomorph
    (X : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (f : X.toOver ⟶ P.toOver) [IsFinite f.left] [Etale f.left] :
    IsLocalHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  let : IsIntegral X.toOver.left := X.property
  obtain ⟨C, g, hg⟩ := Projective.ComponentFactorization.exists_projectiveComponent_factorization P f
  let i := P.componentInclusionOver C
  have he : g.left ≫ i.left = f.left := congrArg (fun k => k.left) hg
  have : IsFinite (g.left ≫ i.left) := he ▸ inferInstanceAs (IsFinite f.left)
  have : Etale (g.left ≫ i.left) := he ▸ inferInstanceAs (Etale f.left)
  have : IsFinite g.left := IsFinite.of_comp g.left i.left
  have : Etale g.left := Etale.of_comp g.left i.left
  have hh := ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion i).isLocalHomeomorph).comp
    (Projective.EtaleCovering.projectiveFiniteEtale_isCoveringMap X (P.componentVariety C) g).isLocalHomeomorph
  change IsLocalHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (g ≫ i)) at hh
  rwa [hg] at hh

theorem finiteEtale_isLocalHomeomorph
    (P Q : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (f : P.toOver ⟶ Q.toOver) [IsFinite f.left] [Etale f.left] :
    IsLocalHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  intro x
  obtain ⟨⟨C, p⟩, hp⟩ := P.componentPointsHomeomorph.surjective x
  let i := P.componentInclusionOver C
  have : IsFinite (i ≫ f).left := inferInstanceAs (IsFinite (i.left ≫ f.left))
  have : Etale (i ≫ f).left := inferInstanceAs (Etale (i.left ≫ f.left))
  have hfi : IsLocalHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f ∘ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) :=
    integralToProjectiveFiniteEtale_isLocalHomeomorph (P.componentVariety C) Q (i ≫ f)
  have hi := (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.isOpenEmbedding_map_of_isOpenImmersion i).isLocalHomeomorph
  have hl := hfi.isLocalHomeomorphOn.of_comp_right
    (show IsLocalHomeomorphOn (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map i) Set.univ from hi.isLocalHomeomorphOn)
  exact hl x ⟨p, Set.mem_univ p, hp⟩

theorem finiteEtale_isCoveringMap
    (P Q : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (f : P.toOver ⟶ Q.toOver) [IsFinite f.left] [Etale f.left] :
    IsCoveringMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) :=
  AlgebraicGeometry.Cycles.Functoriality.Covering.Construction.covering_of_proper_localHomeomorph _
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map f).isProperMap
    (finiteEtale_isLocalHomeomorph P Q f)

theorem finiteEtale_finite_fiber
    (P Q : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (f : P.toOver ⟶ Q.toOver) [IsFinite f.left] [Etale f.left]
    (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Q.toOver) : ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) ⁻¹' {y}).Finite :=
  AlgebraicGeometry.Cycles.Functoriality.Covering.Construction.finite_fiber_of_proper_localHomeomorph _
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map f).isProperMap
    (finiteEtale_isLocalHomeomorph P Q f) y

end

end OAI.RepresentationTheory.Theta.Geometric.SmoothProjectiveCovering
