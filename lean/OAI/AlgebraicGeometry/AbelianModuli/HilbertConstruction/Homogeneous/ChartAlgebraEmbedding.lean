import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.SubalgebraChartEmbedding
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.LocalizationFlat

/-! # Chart Algebra Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartAlgebraEmbedding

noncomputable section

/-! The ambient chart embedding preserves the coefficient algebra.
Polynomial evaluation therefore commutes with this injective embedding. -/
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.LocalizationFlat.GradedHilbert
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
variable (S : Subalgebra R A) (g : ℕ → Submodule R S) [GradedAlgebra g] (f : S)

attribute [local instance] SubalgebraChartEmbedding.chartLocalization

theorem homogeneousSubalgebraChartEmbedding_coefficients (r : R) :
    SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding S g f (algebraMap R (HomogeneousLocalization.Away g f) r) =
      algebraMap R (Localization.Away f.val) r := by
  rw [HilbertScheme.Presentations.Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap]
  change IsLocalization.Away.map (Localization.Away f) (Localization.Away f.val) S.val.toRingHom f
      (Localization.mk (algebraMap R S r) 1) = _
  rw [IsLocalization.Away.map, Localization.mk_eq_mk', IsLocalization.map_mk']
  change IsLocalization.mk' (Localization.Away f.val) (algebraMap R A r) 1 = _
  rw [IsLocalization.mk'_one, ← IsScalarTower.algebraMap_apply]

def homogeneousSubalgebraChartAlgEmbedding :
    HomogeneousLocalization.Away g f →ₐ[R] Localization.Away f.val where
  __ := SubalgebraChartEmbedding.homogeneousSubalgebraChartEmbedding S g f
  commutes' := homogeneousSubalgebraChartEmbedding_coefficients S g f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ChartAlgebraEmbedding
