import OAI.RepresentationTheory.Theta.Geometric.Finite.ProjectivePresentation
import OAI.RepresentationTheory.Theta.Geometric.SmoothProjectiveCovering

/-! # Etale Analytic Cover -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.EtaleAnalyticCover

noncomputable section

/-! Finite étale maps to a smooth projective complex scheme are genuine
analytic coverings. Projectivity of the source is constructed from finiteness. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem finiteEtale_projectiveTarget_isCoveringMap {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation Y.left Y.hom) [Smooth Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] :
    IsCoveringMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) := by
  let Q : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation := ⟨Y.left, Y.hom, P, inferInstance⟩
  let R := ProjectivePresentation.finiteEtaleSmoothProjectivePresentation P f
  exact SmoothProjectiveCovering.finiteEtale_isCoveringMap R Q f

theorem finiteEtale_projectiveTarget_finite_fiber {X Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation Y.left Y.hom) [Smooth Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] (y : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) :
    ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) ⁻¹' {y}).Finite := by
  let Q : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation := ⟨Y.left, Y.hom, P, inferInstance⟩
  let R := ProjectivePresentation.finiteEtaleSmoothProjectivePresentation P f
  exact SmoothProjectiveCovering.finiteEtale_finite_fiber R Q f y

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.EtaleAnalyticCover
