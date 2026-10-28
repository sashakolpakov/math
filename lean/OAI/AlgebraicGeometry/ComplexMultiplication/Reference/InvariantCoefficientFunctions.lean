import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.CoordinateOneForms
import OAI.AlgebraicGeometry.ComplexMultiplication.AnalyticInvariantCovectors

/-! # Invariant Coefficient Functions -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.InvariantCoefficientFunctions

noncomputable section

section

/-! # Genuine holomorphic functions for invariant cotangent coefficients

These functions live in the unchanged original holomorphic-function algebra.
They come from the actual analytic map and actual target group operations.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "ModelI" => 𝓘(ℂ, E)

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [Group G] [TopologicalSpace G] [ChartedSpace F G] [LieGroup 𝓘(ℂ, F) ω G]

/-- Actual invariant-covector coefficients as original local holomorphic sections. -/
def originalInvariantCoefficient
    (f : ComplexPoint.Basic.ComplexSchemePoint X → G) (hf : ContMDiff ModelI 𝓘(ℂ, F) ω f) (α : F →L[ℂ] ℂ)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (z : ComplexPoint.Basic.ComplexSchemePoint X)
    (hU : (U : Set (ComplexPoint.Basic.ComplexSchemePoint X)) ⊆ (chartAt E z).source)
    (d : OpenPartialHomeomorph G F) (hd : d ∈ atlas F G) (h1 : (1 : G) ∈ d.source)
    (j : Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left)) : ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) := by
  let c := chartAt E z
  let L : E → E →L[ℂ] ℂ := fun y =>
    α.comp (fderiv ℂ (fun w => d ((f (c.symm y))⁻¹ * f (c.symm w))) y)
  have hL : ContDiffOn ℂ ω L c.target := by
    intro y hy
    exact (AnalyticInvariantCovectors.analyticInvariantCovectorCoefficientAlong f hf α c d
      (chart_mem_atlas E z) hd h1 hy).contDiffWithinAt
  have hval : ContDiffOn ℂ ω (fun y => L y (Pi.single j 1)) c.target :=
    hL.clm_apply contDiffOn_const
  have hc : ContMDiff ModelI ModelI ω (fun x : U => c x.val) :=
    (contMDiffOn_chart (I := ModelI) (x := z) (n := ω)).comp_contMDiff
      contMDiff_subtype_val (fun x => hU x.property)
  refine ⟨fun x => L (c x.val) (Pi.single j 1), ?_⟩
  exact hval.contMDiffOn.comp_contMDiff hc
    (fun x => c.map_source (hU x.property))

/-- The holomorphic section retains the actual derivative coefficient. -/
theorem originalInvariantCoefficient_apply
    (f : ComplexPoint.Basic.ComplexSchemePoint X → G) (hf : ContMDiff ModelI 𝓘(ℂ, F) ω f) (α : F →L[ℂ] ℂ)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (z : ComplexPoint.Basic.ComplexSchemePoint X)
    (hU : (U : Set (ComplexPoint.Basic.ComplexSchemePoint X)) ⊆ (chartAt E z).source)
    (d : OpenPartialHomeomorph G F) (hd : d ∈ atlas F G) (h1 : (1 : G) ∈ d.source)
    (j : Fin (Topology.Dimension.Basic.TopologicalSpace.dim X.left)) (x : U) :
    (originalInvariantCoefficient X f hf α U z hU d hd h1 j).1 x =
      (α.comp (fderiv ℂ (fun w => d
        ((f ((chartAt E z).symm ((chartAt E z) x.val)))⁻¹ *
          f ((chartAt E z).symm w))) ((chartAt E z) x.val))) (Pi.single j 1) := rfl

end

/-! # Original holomorphic representatives for invariant cotangent pullbacks

The representative is a sum of actual holomorphic coefficients times actual
chart-coordinate differentials. Evaluation recovers the full covector.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold

private theorem covector_sum_coordinates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → ℂ) →L[ℂ] ℂ) (v : ι → ℂ) :
    ∑ j, L (Pi.single j 1) * v j = L v := by
  have hv : (∑ j, v j • Pi.single j 1) = v := by
    funext k
    simp [Pi.single_apply]
  calc
    ∑ j, L (Pi.single j 1) * v j = ∑ j, v j * L (Pi.single j 1) :=
      Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    _ = L (∑ j, v j • Pi.single j 1) := by simp only [map_sum, map_smul, smul_eq_mul]
    _ = L v := congrArg L hv

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]

local notation "E" => (Fin (OAI.Topology.Dimension.Basic.TopologicalSpace.dim X.left) → ℂ)
local notation "ModelI" => 𝓘(ℂ, E)

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [Group G] [TopologicalSpace G] [ChartedSpace F G] [LieGroup 𝓘(ℂ, F) ω G]

/-- An actual original local Kähler representative for the pulled-back invariant covector. -/
def originalInvariantOneForm
    (f : ComplexPoint.Basic.ComplexSchemePoint X → G) (hf : ContMDiff ModelI 𝓘(ℂ, F) ω f) (α : F →L[ℂ] ℂ)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (z : ComplexPoint.Basic.ComplexSchemePoint X)
    (hU : (U : Set (ComplexPoint.Basic.ComplexSchemePoint X)) ⊆ (chartAt E z).source)
    (d : OpenPartialHomeomorph G F) (hd : d ∈ atlas F G) (h1 : (1 : G) ∈ d.source) :
    Algebra.DeRham.Basic.Form ℂ (ComplexPoint.Basic.ComplexSchemePoint.OpenHolomorphicFunctions X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U)) 1 :=
  CoordinateOneForms.originalCoordinateOneForm X U z (by simpa only [extChartAt_source] using hU)
    (fun j => originalInvariantCoefficient X f hf α U z hU d hd h1 j)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original representative has exactly the actual invariant pullback's chart values. -/
theorem chartEvaluation_originalInvariantOneForm
    (f : ComplexPoint.Basic.ComplexSchemePoint X → G) (hf : ContMDiff ModelI 𝓘(ℂ, F) ω f) (α : F →L[ℂ] ℂ)
    (U : Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (z : ComplexPoint.Basic.ComplexSchemePoint X)
    (hU : (U : Set (ComplexPoint.Basic.ComplexSchemePoint X)) ⊆ (chartAt E z).source)
    (d : OpenPartialHomeomorph G F) (hd : d ∈ atlas F G) (h1 : (1 : G) ∈ d.source)
    {y : E} (hy : y ∈ ComplexPoint.Basic.ComplexSchemePoint.chartSectionDomain X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z)
    (v : Fin 1 → E) :
    ComplexPoint.Basic.ComplexSchemePoint.chartEvaluation X (Topology.Dimension.Basic.TopologicalSpace.dim X.left) (Opposite.op U) z 1
        (originalInvariantOneForm X f hf α U z hU d hd h1) y v =
      (α.comp (fderiv ℂ (fun w => d
        ((f ((chartAt E z).symm y))⁻¹ * f ((chartAt E z).symm w))) y)) (v 0) := by
  rw [originalInvariantOneForm, CoordinateOneForms.chartEvaluation_originalCoordinateOneForm X U z _ _ hy]
  simp only [originalInvariantCoefficient_apply, extChartAt_coe_symm,
    modelWithCornersSelf_coe_symm, Function.comp_def, id_eq]
  have hcy : (chartAt E z) ((chartAt E z).symm y) = y :=
    (chartAt E z).right_inv (by simpa only [extChartAt_target,
      modelWithCornersSelf_coe_symm, modelWithCornersSelf_coe, Set.preimage_id,
      Set.range_id, Set.inter_univ] using hy.1)
  rw [hcy]
  exact covector_sum_coordinates _ (v 0)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.InvariantCoefficientFunctions
