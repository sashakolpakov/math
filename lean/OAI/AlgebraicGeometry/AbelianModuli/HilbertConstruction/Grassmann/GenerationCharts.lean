import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GenerationOpenIndependence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ChartLoci

/-! # Generation Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.GenerationCharts

noncomputable section

/-! The normalized generation opens glue across the genuine Grassmannian quotient charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ α : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ] [Fintype α]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ] [DecidableEq α]
variable {S : Scheme.{u}} {M T : Over S}

def grassmannChartGenerationOpen (a : ι → ν) (b : κ → μ)
    (f : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) (F : α → Matrix μ ν Γ(M.left, ⊤)) : M.left.Opens :=
  Normalized.GenerationOpen.normalizedGenerationOpen a b (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S f) F

omit [Fintype κ] [Fintype α] [DecidableEq κ] [DecidableEq α] in
theorem grassmannChartGenerationOpen_preimage (a : ι → ν) (b : κ → μ)
    (f : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) (F : α → Matrix μ ν Γ(M.left, ⊤)) (x : T ⟶ M) :
    x.left ⁻¹ᵁ grassmannChartGenerationOpen a b f F =
      grassmannChartGenerationOpen a b (x ≫ f) (fun i => (F i).map x.left.appTop.hom) := by
  rw [grassmannChartGenerationOpen, GenerationOpenIndependence.normalizedGenerationOpen_preimage,
    ← ChartLoci.normalizedChartMatrix_comp a x f]
  rfl

theorem grassmannChartGenerationOpen_independent (a a' : ι → ν) (b b' : κ → μ)
    (f : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) (f' : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a' S)
    (g : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart b S) (g' : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart b' S)
    (hf : f ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S = f' ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a' S)
    (hg : g ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap b S = g' ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap b' S)
    (F : α → Matrix μ ν Γ(M.left, ⊤))
    (hF : ∀ i, (Matrix.toLin' (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S f)).ker ≤
      ((Matrix.toLin' (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix b S g)).ker).comap (Matrix.toLin' (F i))) :
    grassmannChartGenerationOpen a b f F = grassmannChartGenerationOpen a' b' f' F :=
  GenerationOpenIndependence.normalizedGenerationOpen_eq_of_kernels a a' b b'
    (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S f) (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a' S f') (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix b S g) (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix b' S g')
    (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized a S f) (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized a' S f')
    (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized b S g) (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized b' S g')
    ((HilbertScheme.Presentations.Quotient.ChartClassifyingMap.Grassmannian.chartMaps_eq_iff_kernel_eq a a' f f').mp hf)
    ((HilbertScheme.Presentations.Quotient.ChartClassifyingMap.Grassmannian.chartMaps_eq_iff_kernel_eq b b' g g').mp hg) F hF

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.GenerationCharts
