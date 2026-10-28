import OAI.AlgebraicGeometry.Comparison.Betti.Projective.Coherent
import OAI.AlgebraicGeometry.Comparison.Betti.Analytification.Term
import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.ExteriorFrames

/-! # Holomorphic Forms Acyclic -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.HolomorphicFormsAcyclic.Dolbeault

noncomputable section

/-! Coherent comparison makes the original holomorphic form sheaves acyclic on projective coordinate intersections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveHolomorphicFormAdditiveSheaf (n r : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n)) :=
  (sheafCompose (Opens.grothendieckTopology (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n))
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj
      ((Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))).X r)

theorem projectiveHolomorphicFormsCechAcyclic (n r : ℕ) :
    SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (Intersections.Dolbeault.projectiveStandardCover n)
      (projectiveHolomorphicFormAdditiveSheaf n r) := by
  let X := Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  let M := Exterior.ModuleSheaf.exteriorFormsModuleSheaf X r
  let : M.IsQuasicoherent := Smooth.ExteriorFrames.smooth_exteriorFormsModuleSheaf_quasicoherent X r
  let : M.IsFiniteType := Smooth.ExteriorFrames.smooth_exteriorFormsModuleSheaf_finiteType X r
  exact Cech.AcyclicShortExact.cechIntersectionsAcyclic_of_iso (X := TopCat.of (ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n))
    (Intersections.Dolbeault.projectiveStandardCover n) (Analytification.Term.analyticExteriorFormForgetIso X r)
      (Coherent.Dolbeault.projectiveAnalyticCechAcyclic_coherent n M)

theorem projectiveExteriorModuleOriginalComparison_isIso (n r q : ℕ) :
    IsIso (HomologicalComplex.homologyMap (ModuleFunctor.Dolbeault.projectiveModuleOriginalCechMap (n + 1)
      (Exterior.ModuleSheaf.exteriorFormsModuleSheaf (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1))) r)) q) := by
  let X := Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase (n + 1))
  let M := Exterior.ModuleSheaf.exteriorFormsModuleSheaf X r
  let : M.IsQuasicoherent := Smooth.ExteriorFrames.smooth_exteriorFormsModuleSheaf_quasicoherent X r
  let : M.IsFiniteType := Smooth.ExteriorFrames.smooth_exteriorFormsModuleSheaf_finiteType X r
  exact Coherent.Dolbeault.projectiveCoherentOriginalComparison_isIso n M q

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.HolomorphicFormsAcyclic.Dolbeault
