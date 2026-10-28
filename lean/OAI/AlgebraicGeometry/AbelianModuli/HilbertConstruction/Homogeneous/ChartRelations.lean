import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GenerationCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.QuotientClassification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.RankAffineCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.HomogeneousGenerators

/-! # Chart Relations -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartRelations

noncomputable section

/-! The homogeneous quotient classified by a normalized chart point has exactly the explicit kernel used in the generated matrix loci. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {M : Over S} {n N r : ℕ}
variable (a : ULift.{u} (Fin r) → ULift.{u} (Coordinates.HomogeneousMonomials (Fin (n + 1)) N))
variable (v : M ⟶ HilbertScheme.Presentations.Normalized.Chart.Grassmannian.normalizedChart a S)

theorem homogeneousChart_affine_relations (R : CommRingCat.{u}) {f : Spec R ⟶ S}
    (x : Over.mk f ⟶ M)
    (U : Module.Grassmannian R (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R N) r)
    (hU : (x ≫ v) ≫ HilbertScheme.Presentations.Grassmannian.Gluing.grassmannianChartOverMap a S =
      QuotientParameters.homogeneousQuotientAffinePointEquiv.{u, 0} (Fin (n + 1)) N r R f U) :
    U.toSubmodule = Normalized.HomogeneousGenerators.normalizedHomogeneousRelations (HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S v) R x) := by
  let e := QuotientParameters.homogeneousLiftedCoordinates.{u, 0} (Fin (n + 1)) N R
  have h := Affine.GenerationCoordinates.grassmannParameterAffine_chart_kernel_coefficients R f
    (QuotientClassification.homogeneousLiftedQuotient.{u, 0} (Fin (n + 1)) N r R U) a (x ≫ v)
    (hU.trans (QuotientClassification.homogeneousQuotientAffinePointEquiv_coordinates (Fin (n + 1)) N r R f U))
  rw [Grassmann.ChartLoci.normalizedChartMatrix_comp] at h
  change (Matrix.toLin' (HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S v) R x)).ker =
    U.toSubmodule.map e.toLinearMap at h
  change U.toSubmodule =
    (Matrix.toLin' (HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients M (HilbertScheme.Presentations.Normalized.AtlasMaps.Grassmannian.chartMatrix a S v) R x)).ker.map e.symm.toLinearMap
  rw [h, ← Submodule.map_comp]
  have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    exact e.symm_apply_apply
  rw [he, Submodule.map_id]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartRelations
