import OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential
import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.Differential

/-! # Parameter Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normal.ParameterRestriction.Constructions

noncomputable section

/-! Restricting actual normal coordinates to a smaller ambient open
set preserves holomorphy, submersion, and the exact zero locus. The
parametrized source need not be globally closed. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.InclusionDifferential.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.Differential.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {M N E F G : Type} [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  {f : M → N} {x : M} (Q : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)
  (U : Opens N) (hU : U ≤ Q.openNeighborhood)

local instance : ChartedSpace G Q.neighborhood := inferInstanceAs (ChartedSpace G Q.openNeighborhood)
local instance (O : Opens N) : ChartedSpace G (O : Set N) := inferInstanceAs (ChartedSpace G O)

def normalParameterInclusion : TopCat.of U ⟶ TopCat.of Q.neighborhood :=
  TopCat.ofHom ⟨fun y => ⟨y.val, hU y.property⟩, continuous_subtype_val.subtype_mk _⟩

def normalParameter : TopCat.of U ⟶ TopCat.of F := normalParameterInclusion Q U hU ≫ Q.normalCoordinate

theorem normalParameter_analytic
    (hQ : ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, E × F) ω Q.ambientChart Q.ambientChart.source) :
    ContMDiff 𝓘(ℂ, G) 𝓘(ℂ, F) ω (normalParameter Q U hU) :=
  (NormalPair.Differential.Constructions.normalCoordinate_analytic Q hQ).comp (Open.InclusionDifferential.Constructions.openInclusion_analytic U Q.openNeighborhood hU)

theorem normalParameter_submersion
    (hQd : Q.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × F))
    (hQ : ContMDiffOn 𝓘(ℂ, G) 𝓘(ℂ, E × F) ω Q.ambientChart Q.ambientChart.source)
    (y : U) : Function.Surjective (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, F) (normalParameter Q U hU) y) := by
  have hi := Open.InclusionDifferential.Constructions.openInclusion_analytic (E := G) U Q.openNeighborhood hU
  have he := mfderiv_comp y
    (((NormalPair.Differential.Constructions.normalCoordinate_analytic Q hQ) (normalParameterInclusion Q U hU y)).mdifferentiableAt (by simp))
    ((hi y).mdifferentiableAt (by simp))
  have hd : mfderiv 𝓘(ℂ, G) 𝓘(ℂ, G) (normalParameterInclusion Q U hU) y = ContinuousLinearMap.id ℂ G :=
    Open.InclusionDifferential.Constructions.openInclusion_mfderiv U Q.openNeighborhood hU y
  rw [hd] at he
  change mfderiv 𝓘(ℂ, G) 𝓘(ℂ, F) (normalParameter Q U hU) y =
    (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, F) Q.normalCoordinate (normalParameterInclusion Q U hU y)).comp
      (ContinuousLinearMap.id ℂ G) at he
  exact (congrArg (fun L : G →L[ℂ] F => Function.Surjective L) he).mpr
    (NormalPair.Differential.Constructions.normalCoordinate_submersion Q hQd (normalParameterInclusion Q U hU y))

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
theorem normalParameter_zero_iff (y : U) : normalParameter Q U hU y = 0 ↔ y.val ∈ Set.range f :=
  (Q.mem_range_iff (normalParameterInclusion Q U hU y)).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normal.ParameterRestriction.Constructions
