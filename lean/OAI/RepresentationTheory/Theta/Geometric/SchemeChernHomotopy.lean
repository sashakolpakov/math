import OAI.RepresentationTheory.Theta.Geometric.SchemeChernPullback
import OAI.RepresentationTheory.Theta.Geometric.CocycleClassNaturality

/-! # Scheme Chern Homotopy -/

namespace OAI.RepresentationTheory.Theta.Geometric.SchemeChernHomotopy

noncomputable section

/-! Homotopies into an arbitrary total complex scheme compare the
original native Chern classes on different smooth projective fibers. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left}

theorem native_chernClass_eq_of_homotopic (Y Z : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (f : Y.toOver ⟶ X) (g : Z.toOver ⟶ X)
    {T : TopCat} [CompactSpace T] [T2Space T]
    (p : T ⟶ TopCat.of (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y.toOver))
    (q : T ⟶ TopCat.of (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z.toOver))
    (h : (p ≫ TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)).hom.Homotopic
      (q ≫ TopCat.ofHom (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous g)).hom) :
    AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) p 2
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass Y (L.pullback f.left)) =
      AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) q 2
        (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernClasses.lineBundleChernClass Z (L.pullback g.left)) := by
  let A := SchemeLineFrame.schemeLineAtlas L
  rw [← A.pullback_chernClass_native_compact Y f p, ← A.pullback_chernClass_native_compact Z g q]
  exact A.continuousCocycle.chernClass_homotopic_compact_source _ _ h

end

end OAI.RepresentationTheory.Theta.Geometric.SchemeChernHomotopy
