import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ChartCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Common.OpenCover

/-! # Pair Chart Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.PairChartCover

noncomputable section

/-! A constructed common normalized-chart cover for two Grassmannian parameter maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {ι ν κ μ : Type u} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {S : Scheme.{u}} {M : Over S}
variable (q : M ⟶ ParameterScheme.grassmannParameterScheme (ι := ι) (ν := ν) S)
variable (k : M ⟶ ParameterScheme.grassmannParameterScheme (ι := κ) (ν := μ) S)

structure GrassmannPairChartCover where
  cover : M.left.OpenCover
  sourceColumns : cover.I₀ → (ι → ν)
  targetColumns : cover.I₀ → (κ → μ)
  sourceLift : ∀ i, Embedded.FamilyOpenCover.overOpenCoverObject M cover i ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart (sourceColumns i) S
  targetLift : ∀ i, Embedded.FamilyOpenCover.overOpenCoverObject M cover i ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart (targetColumns i) S
  source_fac : ∀ i, sourceLift i ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap (sourceColumns i) S =
    Embedded.FamilyOpenCover.overOpenCoverMap M cover i ≫ q
  target_fac : ∀ i, targetLift i ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap (targetColumns i) S =
    Embedded.FamilyOpenCover.overOpenCoverMap M cover i ≫ k

def grassmannPairChartCover : GrassmannPairChartCover q k where
  cover := Common.OpenCover.commonOpenCover M (ChartCover.grassmannMapChartCover q) (ChartCover.grassmannMapChartCover k)
  sourceColumns p := p.1
  targetColumns p := p.2
  sourceLift p := Common.OpenCover.commonOpenCoverLeft M _ _ p.1 p.2 ≫ ChartCover.grassmannMapChartLift q p.1
  targetLift p := Common.OpenCover.commonOpenCoverRight M _ _ p.1 p.2 ≫ ChartCover.grassmannMapChartLift k p.2
  source_fac p := by
    let l := Common.OpenCover.commonOpenCoverLeft M (ChartCover.grassmannMapChartCover q) (ChartCover.grassmannMapChartCover k) p.1 p.2
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => l ≫ f) (ChartCover.grassmannMapChartLift_fac q p.1)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun f => f ≫ q) (Common.OpenCover.commonOpenCoverLeft_map M _ _ p.1 p.2))))
  target_fac p := by
    let l := Common.OpenCover.commonOpenCoverRight M (ChartCover.grassmannMapChartCover q) (ChartCover.grassmannMapChartCover k) p.1 p.2
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun f => l ≫ f) (ChartCover.grassmannMapChartLift_fac k p.2)).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun f => f ≫ k) (Common.OpenCover.commonOpenCoverRight_map M _ _ p.1 p.2))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.PairChartCover
