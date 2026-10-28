import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.IncidenceIdeals
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ChartClassifyingMap

/-! # Chart Loci -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ChartLoci

noncomputable section

/-!
Incidence ideals for two Grassmannian chart maps. Their vanishing criterion
uses the actual quotient kernels, so the ideals are independent of chart choices.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ChartClassifyingMap.Grassmannian

universe u

variable {ι ν κ μ : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ]
variable {S : Scheme.{u}} {M T : Over S}

omit [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ]
  [DecidableEq ν] [DecidableEq κ] [DecidableEq μ] in
theorem normalizedChartMatrix_comp (a : ι → ν) (f : T ⟶ M) (g : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) :
    HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S (f ≫ g) = (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S g).map f.left.appTop.hom := by
  unfold HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix
  rw [HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChartRepresentation_apply, HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChartRepresentation_apply]
  rfl

def grassmannChartIncidenceIdeal (a : ι → ν) (b : κ → μ)
    (f : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) (g : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart b S)
    (F : Matrix μ ν Γ(M.left, ⊤)) : M.left.IdealSheafData :=
  Normalized.IncidenceIdeals.normalizedIncidenceIdeal M a (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S f) (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized a S f)
    (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix b S g) F

omit [Fintype κ] in
theorem grassmannChartIncidenceIdeal_vanish_iff (a : ι → ν) (b : κ → μ)
    (f : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) (g : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart b S)
    (F : Matrix μ ν Γ(M.left, ⊤)) (x : T ⟶ M) :
    (grassmannChartIncidenceIdeal a b f g F).comap x.left = ⊥ ↔
      (Matrix.toLin' (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S (x ≫ f))).ker ≤
        ((Matrix.toLin' (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix b S (x ≫ g))).ker).comap
          (Matrix.toLin' (F.map x.left.appTop.hom)) := by
  rw [grassmannChartIncidenceIdeal, Normalized.IncidenceIdeals.normalizedIncidenceIdeal_vanish_iff]
  rw [normalizedChartMatrix_comp, normalizedChartMatrix_comp]
  rfl

theorem grassmannChartIncidenceIdeal_chart_independent (a a' : ι → ν) (b b' : κ → μ)
    (f : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) (f' : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a' S)
    (g : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart b S) (g' : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart b' S)
    (hf : f ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S = f' ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a' S)
    (hg : g ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap b S = g' ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap b' S)
    (F : Matrix μ ν Γ(M.left, ⊤)) :
    grassmannChartIncidenceIdeal a b f g F = grassmannChartIncidenceIdeal a' b' f' g' F := by
  apply Closed.ConditionIdeals.ideal_eq_of_vanishing_iff
  intro U x
  let x' : Over.mk (x ≫ M.hom) ⟶ M := Over.homMk x rfl
  change (grassmannChartIncidenceIdeal a b f g F).comap x'.left = ⊥ ↔
    (grassmannChartIncidenceIdeal a' b' f' g' F).comap x'.left = ⊥
  rw [grassmannChartIncidenceIdeal_vanish_iff, grassmannChartIncidenceIdeal_vanish_iff]
  have hq := (HilbertScheme.Presentations.Quotient.ChartClassifyingMap.Grassmannian.chartMaps_eq_iff_kernel_eq a a' (x' ≫ f) (x' ≫ f')).mp
    (by simpa only [Category.assoc] using congrArg (fun k => x' ≫ k) hf)
  have hk := (HilbertScheme.Presentations.Quotient.ChartClassifyingMap.Grassmannian.chartMaps_eq_iff_kernel_eq b b' (x' ≫ g) (x' ≫ g')).mp
    (by simpa only [Category.assoc] using congrArg (fun k => x' ≫ k) hg)
  rw [hq, hk]

omit [Fintype κ] in
theorem grassmannChartIncidenceIdeal_comap (a : ι → ν) (b : κ → μ)
    (f : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) (g : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart b S)
    (F : Matrix μ ν Γ(M.left, ⊤)) (x : T ⟶ M) :
    (grassmannChartIncidenceIdeal a b f g F).comap x.left =
      grassmannChartIncidenceIdeal a b (x ≫ f) (x ≫ g) (F.map x.left.appTop.hom) := by
  apply Closed.ConditionIdeals.ideal_eq_of_vanishing_iff
  intro U y
  let y' : Over.mk (y ≫ T.hom) ⟶ T := Over.homMk y rfl
  change ((grassmannChartIncidenceIdeal a b f g F).comap x.left).comap y'.left = ⊥ ↔
    (grassmannChartIncidenceIdeal a b (x ≫ f) (x ≫ g)
      (F.map x.left.appTop.hom)).comap y'.left = ⊥
  rw [← Scheme.IdealSheafData.comap_comp]
  change (grassmannChartIncidenceIdeal a b f g F).comap (y' ≫ x).left = ⊥ ↔ _
  rw [grassmannChartIncidenceIdeal_vanish_iff, grassmannChartIncidenceIdeal_vanish_iff]
  simp only [Category.assoc]
  rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ChartLoci
