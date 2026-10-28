import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.IncidenceCondition

/-! # Incidence Normalized Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IncidenceNormalizedCriterion

noncomputable section

/-! A single pair of normalized charts detects the full intrinsic incidence condition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ : Type u}
variable [Fintype ι] [Fintype ν] [Fintype κ] [Fintype μ]
variable [DecidableEq ι] [DecidableEq ν] [DecidableEq κ] [DecidableEq μ]
variable {S : Scheme.{u}} {M T : Over S}
variable (q : M ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
variable (k : M ⟶ Grassmann.ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S)
variable (F : Matrix μ ν Γ(M.left, ⊤)) (x : T ⟶ M)

theorem grassmannIncidenceCondition_normalized (a : ι → ν) (b : κ → μ)
    (v : T ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) (w : T ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart b S)
    (hv : v ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S = x ≫ q)
    (hw : w ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap b S = x ≫ k) :
    Grassmann.IncidenceCondition.GrassmannIncidenceCondition q k F x ↔
      (Matrix.toLin' (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S v)).ker ≤
        ((Matrix.toLin' (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix b S w)).ker).comap
          (Matrix.toLin' (F.map x.left.appTop.hom)) := by
  rw [← Grassmann.IncidenceCondition.grassmannIncidenceIdeal_vanish_iff, Grassmann.IncidenceChartRecognition.grassmannIncidenceIdeal_baseChange]
  have he := (Grassmann.PairChartCover.grassmannPairChartCover (x ≫ q) (x ≫ k)).incidenceIdeal_eq_chart
    (F.map x.left.appTop.hom) a b v w hv hw
  change Grassmann.IncidenceScheme.grassmannIncidenceIdeal (x ≫ q) (x ≫ k) (F.map x.left.appTop.hom) =
    Grassmann.ChartLoci.grassmannChartIncidenceIdeal a b v w (F.map x.left.appTop.hom) at he
  rw [he]
  exact Grassmann.IncidenceCondition.grassmannChartIncidenceIdeal_eq_bot_iff (F.map x.left.appTop.hom) a b v w

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IncidenceNormalizedCriterion
