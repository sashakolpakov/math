import OAI.AlgebraicTopology.DeRham.Comparison.CechTotal
import OAI.AlgebraicTopology.DeRham.Comparison.CechComplexAugmentation
import OAI.AlgebraicTopology.Cohomology.Singular.ChartOpenDiffeomorph
import OAI.AlgebraicTopology.DeRham.Comparison.Euclidean
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexDiffeomorph
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldCechAugmentationBridge
import OAI.AlgebraicTopology.DeRham.Comparison.IntegrationEvaluation
import OAI.AlgebraicTopology.Cohomology.Singular.ManifoldSmoothCechComparison

/-! # Manifold -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.Manifold

noncomputable section

/-!
# Global comparison by genuine finite chart descent

Every intersection of a finite chart-source cover is contained in its first
chart. The actual restricted chart identifies it with an open model domain;
this is the geometric input for descent of the Duffy integration map.
-/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite Set
open scoped _root_.Manifold ContDiff

section ChartCover

variable (E M : Type) [TopologicalSpace E] [TopologicalSpace M] [ChartedSpace E M]

/-- The actual source of the chart chosen at a point, as an open subset. -/
def manifoldChartOpen (x : M) : Opens M :=
  ⟨(chartAt E x).source, (chartAt E x).open_source⟩

/-- Compactness selects a finite cover by actual chart sources. -/
theorem exists_finite_manifoldChartOpen_cover [CompactSpace M] :
    ∃ centers : Finset M, ∀ y : M,
      ∃ x : centers, y ∈ manifoldChartOpen E M x.val := by
  classical
  obtain ⟨centers, hcover⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M => (chartAt E x).source) (fun x => (chartAt E x).open_source)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, mem_chart_source E y⟩)
  refine ⟨centers, ?_⟩
  intro y
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_univ y))
  exact ⟨⟨x, hx⟩, hy⟩

/-- Every ordered chart intersection is contained in its first chart source. -/
theorem cechChartIntersection_subset (centers : Finset M) {p : ℕ}
    (a : Fin (p + 1) → centers) :
    (SmoothCech.cechIntersection (fun x : centers => manifoldChartOpen E M x.val) a : Set M) ⊆
      (chartAt E (a 0).val).source :=
  SmoothCech.cechIntersection_le (fun x : centers => manifoldChartOpen E M x.val) a 0

end ChartCover

section ManifoldTop

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [TopologicalSpace M] [ChartedSpace E M]

/-- The top open submanifold is genuinely diffeomorphic to the original manifold. -/
def manifoldTopDiffeomorph :
    Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (⊤ : Opens M) M ∞ where
  toEquiv := Equiv.Set.univ M
  contMDiff_toFun := contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (⊤ : Opens M) _).mp
    exact contMDiff_id

end ManifoldTop

section LocalComparison

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- On an arbitrary chart subdomain, actual integration is transported from
the proved comparison on its actual open image in the model space. -/
theorem manifoldOpenIntegration_quasiIso_chartOpen (x : M) (W : Opens M)
    (hW : (W : Set M) ⊆ (chartAt E x).source) :
    QuasiIso (ManifoldOpenIntegration.manifoldOpenIntegration E W) :=
  (SmoothSimplexDiffeomorph.quasiIso_manifoldOpenIntegration_diffeomorph_iff W (Cohomology.Singular.ChartOpenDiffeomorph.chartOpenImage E x W hW)
    (Cohomology.Singular.ChartOpenDiffeomorph.chartOpenDiffeomorph E x W hW)).mp
      (Euclidean.manifoldOpenIntegration_quasiIso_euclideanOpen E (Cohomology.Singular.ChartOpenDiffeomorph.chartOpenImage E x W hW))

/-- Every ordered intersection of actual chart sources has the genuine
local integration comparison, including empty intersections. -/
theorem manifoldChartIntersection_integration_quasiIso (centers : Finset M) (p : ℕ)
    (a : Fin (p + 1) → centers) :
    QuasiIso (CechColumns.cechIntersectionMap
      (fun x : centers => manifoldChartOpen E M x.val)
      (ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M) a) := by
  apply (IntegrationEvaluation.manifoldOpenIntegrationIntersection_quasiIso_iff E M
    (fun x : centers => manifoldChartOpen E M x.val) a).mpr
  exact manifoldOpenIntegration_quasiIso_chartOpen E M (a 0).val _
    (cechChartIntersection_subset E M centers a)

end LocalComparison

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M]

/-- Finite chart descent proves the actual top-open integration map is a
quasi-isomorphism. Both augmentations and all local comparisons are proved. -/
theorem manifoldOpenIntegration_quasiIso_top_of_compact :
    QuasiIso (ManifoldOpenIntegration.manifoldOpenIntegration E (⊤ : Opens M)) := by
  classical
  obtain ⟨centers, hcover⟩ := exists_finite_manifoldChartOpen_cover E M
  let U : centers → Opens M := fun x => manifoldChartOpen E M x.val
  apply (IntegrationEvaluation.manifoldOpenIntegrationPresheafMap_quasiIso_iff E M (⊤ : Opens M)).mp
  apply CechComplexAugmentation.cechTotalAugmentation_quasiIso_descent U ⊤ (fun _ => le_top)
    (ManifoldOpenIntegration.manifoldOpenIntegrationPresheafMap E M)
  · exact ManifoldCechAugmentationBridge.manifoldPresheafCechAugmentation_quasiIso E M U hcover
  · exact Cohomology.Singular.ManifoldSmoothCechComparison.manifoldSmoothCechTopAugmentation_quasiIso E M U hcover
  · apply CechTotal.cechTotalMap_quasiIso_of_intersections
    intro p a
    exact manifoldChartIntersection_integration_quasiIso E M centers p a

/-- Global Duffy integration is a quasi-isomorphism on every compact
Hausdorff finite-dimensional smooth real manifold. -/
theorem smoothSimplexIntegrationCochainMap_quasiIso_compact :
    QuasiIso (SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M) := by
  apply (SmoothSimplexDiffeomorph.quasiIso_smoothSimplexIntegration_diffeomorph_iff (manifoldTopDiffeomorph E M)).mpr
  exact (SmoothSimplexDiffeomorph.quasiIso_manifoldOpenIntegration_iff E (⊤ : Opens M)).mp
    (manifoldOpenIntegration_quasiIso_top_of_compact E M)

/-- The global comparison on cohomology is induced by the genuine
integration map, not by choosing an arbitrary vector-space isomorphism. -/
def manifoldDeRhamSmoothCohomologyIso (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology E M n ≅
      (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).homology n := by
  let : QuasiIso (SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M) :=
    smoothSimplexIntegrationCochainMap_quasiIso_compact E M
  exact isoOfQuasiIsoAt (SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M) n

@[simp]
theorem manifoldDeRhamSmoothCohomologyIso_hom (n : ℕ) :
    (manifoldDeRhamSmoothCohomologyIso E M n).hom =
      SimplexIntegrationCochain.smoothSimplexIntegrationCohomologyMap E M n := rfl

/-- The global comparison sends a cocycle class to the class of its actual
integration cochain. -/
theorem manifoldDeRhamSmoothCohomologyIso_class (n : ℕ) :
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M).homologyπ n ≫ (manifoldDeRhamSmoothCohomologyIso E M n).hom =
      HomologicalComplex.cyclesMap (SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M) n ≫
        (Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).homologyπ n :=
  HomologicalComplex.homologyπ_naturality (SimplexIntegrationCochain.smoothSimplexIntegrationCochainMap E M) n

end

end OAI.AlgebraicTopology.DeRham.Comparison.Manifold
