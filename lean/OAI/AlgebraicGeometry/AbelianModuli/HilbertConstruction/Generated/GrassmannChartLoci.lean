import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GeneratedRankLoci
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartRelations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.DegreeAffineLifting

/-! # Grassmann Chart Loci -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.GrassmannChartLoci

noncomputable section

/-! Each normalized Grassmann chart has an actual locally closed locus whose affine points are exactly the generated-parameter lifts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) (n B : ℕ) (r : ℕ → ℕ) (N : ℕ)
variable (a : ULift.{u} (Fin (r N)) → ULift.{u} (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N))

def generatedGrassmannChartSubfunctor : Subfunctor (yoneda.obj (HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S)) :=
  Normalized.GeneratedRankLoci.normalizedGeneratedRankSubfunctor (HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) a
    (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S (𝟙 (HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S))) B r

theorem generatedGrassmannChart_immersion :
    HilbertScheme.Presentations.SubfunctorRepresentations.ImmersionRepresentable (generatedGrassmannChartSubfunctor S n B r N a) :=
  Normalized.GeneratedRankLoci.normalizedGeneratedRank_immersion (HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) a
    (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S (𝟙 (HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S))) B r

theorem generatedGrassmannChart_affine_lift_iff (hN : N ≤ B)
    (R : CommRingCat.{u}) (f : Spec R ⟶ S) (x : Over.mk f ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) :
    x ∈ (generatedGrassmannChartSubfunctor S n B r N a).obj (.op (Over.mk f)) ↔
      ∃! y : Over.mk f ⟶ Truncated.GeneratedParameters.truncatedGeneratedParameters S n B r N,
        y ≫ DegreeProjection.truncatedGeneratedDegreeProjection S n B r N hN = x ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S := by
  let q : Over.mk f ⟶ Homogeneous.QuotientParameters.homogeneousQuotientParameterScheme.{u, 0} (Fin (n + 1)) N (r N) S :=
    x ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S
  let U := (Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) N (r N) R f).symm q
  have hU : (x ≫ 𝟙 (HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S)) ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S =
      Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) N (r N) R f U := by
    rw [Category.comp_id]
    exact ((Homogeneous.QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) N (r N) R f).apply_symm_apply q).symm
  have hrel := Homogeneous.ChartRelations.homogeneousChart_affine_relations a (𝟙 (HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S)) R x U hU
  exact (Normalized.GeneratedRankLoci.normalizedGeneratedRank_affine_iff (HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S) a
    (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S (𝟙 (HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S))) B r
    (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized a S (𝟙 (HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S))) R x U hrel).trans
      (DegreeAffineLifting.generatedDegreeProjection_affine_lift_iff hN R f q)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.GrassmannChartLoci
