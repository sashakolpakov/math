import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.CovectorDimension
import OAI.AlgebraicGeometry.AbelianVariety.PureAverage

/-! # Invariant Holomorphic Dimension -/

namespace OAI.RepresentationTheory.Theta.Geometric.InvariantHolomorphicDimension

noncomputable section

/-! Translation-invariant holomorphic one-forms are determined by a
pure covector at the identity and have the complex tangent dimension. -/

open OAI.AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology
open scoped _root_.Manifold ContDiff

variable (E G : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
    [Group G] [TopologicalSpace G] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ, E) ∞ G] [LieGroup 𝓘(ℂ, E) ∞ G]

def invariantHolomorphicSubmodule :
    Submodule ℂ (AlgebraicGeometry.AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) 1) :=
  (Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule E G 1 0).comap (AlgebraicGeometry.AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantForms (E := E) (G := G) 1).subtype

def invariantHolomorphicChartEquiv :
    invariantHolomorphicSubmodule E G ≃ₗ[ℂ] Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E 1 0 where
  toFun form := ⟨AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv 1 form.val, by
    rw [AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv_apply]
    have hf : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E G 1 0 form.val.val.val := form.property
    exact (AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantForm_pure_iff (p := 1) (q := 0) form.val).mp hf⟩
  invFun α := ⟨(AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv 1).symm α.val, by
    apply (AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantForm_pure_iff (p := 1) (q := 0) _).mpr
    rw [← AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv_apply, LinearEquiv.apply_symm_apply]
    exact α.property⟩
  left_inv form := Subtype.ext ((AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv 1).symm_apply_apply form.val)
  right_inv α := Subtype.ext ((AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv 1).apply_symm_apply α.val)
  map_add' form other := Subtype.ext ((AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv 1).map_add form.val other.val)
  map_smul' c form := Subtype.ext ((AlgebraicGeometry.AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv 1).map_smul c form.val)

instance invariantHolomorphic_finiteDimensional :
    FiniteDimensional ℂ (invariantHolomorphicSubmodule E G) :=
  (invariantHolomorphicChartEquiv E G |>.trans (Holomorphic.CovectorDimension.holomorphicCovectorDualEquiv E)).symm.finiteDimensional

theorem invariantHolomorphic_finrank :
    Module.finrank ℂ (invariantHolomorphicSubmodule E G) = Module.finrank ℂ E :=
  (invariantHolomorphicChartEquiv E G).finrank_eq.trans (Holomorphic.CovectorDimension.holomorphicCovector_finrank E)

end

end OAI.RepresentationTheory.Theta.Geometric.InvariantHolomorphicDimension
