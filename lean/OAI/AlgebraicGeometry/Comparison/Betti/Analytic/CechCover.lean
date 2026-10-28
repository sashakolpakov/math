import OAI.AlgebraicGeometry.Comparison.Betti.Open.SmoothForms
import OAI.AlgebraicGeometry.Comparison.Betti.SeparatedPointTopology
import OAI.AlgebraicGeometry.Comparison.Betti.SigmaCompactIntegration

/-! # Cech Cover -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Analytic.CechCover

noncomputable section

/-! Actual analytified Zariski covers compute smooth de Rham cohomology by partition of unity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

theorem finiteType_complexPoints_sigmaCompact [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] :
    SigmaCompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := by
  have : LocallyCompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_locallyCompact X
  have : SecondCountableTopology (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := ComplexPoints.Analytic.FiniteTypeSchemeTopology.schemePoints_secondCountable X
  infer_instance

theorem analyticOpen_cover {ι : Type} (U : ι → X.left.Opens) (hU : ⨆ i, U i = ⊤) :
    ∀ x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X, ∃ i, x ∈ Open.AffineIsoEvaluation.analyticOpen X (U i) := by
  intro x
  have hx : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ ⨆ i, U i := by
    rw [hU]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact ⟨i, hi⟩

variable [IsIntegral X.left] [Smooth X.hom] [IsSeparated X.hom] [QuasiCompact X.hom]
  {ι : Type} (U : ι → X.left.Opens) (hU : ⨆ i, U i = ⊤)

include hU in
theorem analyticCechAugmentation_quasiIso :
    QuasiIso (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := RegularSmoothness.NativeModel X)
      (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i))) := by
  have : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := SeparatedPointTopology.separated_complexPoints_t2Space X
  have : SigmaCompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := finiteType_complexPoints_sigmaCompact X
  exact Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal_quasiIso (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i))
    (analyticOpen_cover X U hU)

def analyticCechCohomologyIso (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) n ≅
      (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := RegularSmoothness.NativeModel X) (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i))).homology n := by
  have : T2Space (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := SeparatedPointTopology.separated_complexPoints_t2Space X
  have : SigmaCompactSpace (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) := finiteType_complexPoints_sigmaCompact X
  exact Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechDeRhamCohomologyIso (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i))
    (analyticOpen_cover X U hU) n

end

end OAI.AlgebraicGeometry.Comparison.Betti.Analytic.CechCover
