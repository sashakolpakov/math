import OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedCoherentAnalyticAcyclicity
import OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedReferenceForm

/-! # Embedded Holomorphic Acyclicity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedHolomorphicAcyclicity

noncomputable section

/-! The independent native holomorphic form sheaves are acyclic on the induced coordinate cover of a smooth integral projective closed subvariety. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

attribute [local instance] Projective.IntersectionHolomorphy.Dolbeault.projectiveIntegral Projective.IntersectionHolomorphy.Dolbeault.projectiveSmooth Projective.IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def nativeHolomorphicFormAdditiveSheaf (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral X.left] [Smooth X.hom] (r : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)) :=
  (sheafCompose (Opens.grothendieckTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (forget₂ (ModuleCat.{0} ℂ) AddCommGrpCat.{0})).obj ((Algebraic.HolomorphicSheafMap.analyticHolomorphicSheafComplex X).X r)

theorem embeddedHolomorphicFormsCechAcyclic
    (n : ℕ) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]
    (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) [IsClosedImmersion f.left] (r : ℕ) :
    SheafCohomology.Cech.VerticalComparison.TopCat.Sheaf.CechIntersectionsAcyclic (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
      (fun i => Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i))
      (nativeHolomorphicFormAdditiveSheaf X r) := by
  let M := Exterior.ModuleSheaf.exteriorFormsModuleSheaf X r
  let : M.IsQuasicoherent := Betti.Smooth.ExteriorFrames.smooth_exteriorFormsModuleSheaf_quasicoherent X r
  let : M.IsFiniteType := Betti.Smooth.ExteriorFrames.smooth_exteriorFormsModuleSheaf_finiteType X r
  exact Cech.AcyclicShortExact.cechIntersectionsAcyclic_of_iso (X := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))
    (fun i => Open.AffineIsoEvaluation.analyticOpen X (f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i))
    (Analytification.Term.analyticExteriorFormForgetIso X r) (EmbeddedCoherentAnalyticAcyclicity.embeddedCoherent_analyticCechIntersectionsAcyclic n X f M)

theorem embeddedProjectiveCoordinateCover_affine
    (n : ℕ) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n))
    [IsClosedImmersion f.left] (i : Fin (n + 1)) :
    IsAffineOpen (f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) :=
  (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen_isAffine n i).preimage f.left

theorem embeddedProjectiveCoordinateCover_covers
    (n : ℕ) (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) (f : X ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) :
    (⨆ i, f.left ⁻¹ᵁ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) = ⊤ :=
  f.left.iSup_preimage_eq_top (Foundations.Scheme.ProjectiveCoordinateCover.iSup_projectiveCoordinateOpen n)

end

end OAI.AlgebraicGeometry.Comparison.Betti.EmbeddedHolomorphicAcyclicity
