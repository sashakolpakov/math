import OAI.AlgebraicGeometry.Cycles.Functoriality.Covering
import OAI.AlgebraicGeometry.Betti.ProjectiveCohomology

/-! # Etale Covering -/

namespace OAI.RepresentationTheory.Theta.Geometric.Projective.EtaleCovering

noncomputable section

/-! Finite étale maps between the original smooth integral projective
models are covering maps on their actual complex points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X Y : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

theorem projectiveFiniteEtale_isCoveringMap (f : X.toOver ⟶ Y.toOver)
    [IsFinite f.left] [Etale f.left] : IsCoveringMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : IsIntegral Y.toOver.left := Y.property
  let : Smooth Y.toOver.hom := Y.presentation.smooth
  exact AlgebraicGeometry.Cycles.Functoriality.Covering.Construction.covering_of_proper_localHomeomorph _
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map f).isProperMap
    (AlgebraicGeometry.Cycles.Functoriality.IntrinsicEtale.Construction.isLocalDiffeomorph_nativeScheme_affineEtale f).isLocalHomeomorph

theorem projectiveFiniteEtale_finite_fiber (f : X.toOver ⟶ Y.toOver)
    [IsFinite f.left] [Etale f.left] (y : Y.analyticSpace) :
    ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) ⁻¹' {y}).Finite := by
  let : IsIntegral X.toOver.left := X.property
  let : Smooth X.toOver.hom := X.presentation.smooth
  let : IsIntegral Y.toOver.left := Y.property
  let : Smooth Y.toOver.hom := Y.presentation.smooth
  exact AlgebraicGeometry.Cycles.Functoriality.Covering.Construction.finite_fiber_of_proper_localHomeomorph _
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map f).isProperMap
    (AlgebraicGeometry.Cycles.Functoriality.IntrinsicEtale.Construction.isLocalDiffeomorph_nativeScheme_affineEtale f).isLocalHomeomorph y

end

end OAI.RepresentationTheory.Theta.Geometric.Projective.EtaleCovering
