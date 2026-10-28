import OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion
import OAI.AlgebraicGeometry.CycleClass.Thom.EquationNormalPair
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Manifold Equation Coordinates -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.ManifoldEquationCoordinates.Constructions

noncomputable section

/-! Native manifold submersions give genuine normal coordinates for
their embedded zero locus. The derivative is the actual manifold
derivative, transported through the preferred ambient chart. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped ContDiff _root_.Manifold _root_.Topology

open OAI.AlgebraicGeometry.CycleClass.Thom.Closed.ComplexImmersion.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EquationNormalPair.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Closed.ComplexImmersion.Constructions.ComplexManifold} {p : ℕ} (Z : Closed.ComplexImmersion.Constructions.ClosedComplexImmersion V p)

theorem exists_equation_normalPair (f : V.analyticSpace → (Fin p → ℂ))
    (x : Z.regularAnalyticSpace)
    (hf : ContMDiffAt 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Fin p → ℂ) ω f
      (Z.regularComplementInclusion x))
    (hs : Function.Surjective (mfderiv 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Fin p → ℂ) f
      (Z.regularComplementInclusion x)))
    (U : Opens V.analyticSpace) (hxU : Z.regularComplementInclusion x ∈ U)
    (hzero : ∀ y ∈ U, y ∈ Set.range Z.regularComplementInclusion ↔ f y = 0) :
    ∃ P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair Z.regularAnalyticModel (Fin p → ℂ) Z.regularComplementInclusion x,
      P.neighborhood ⊆ U ∧
      P.ambientChart.MDifferentiable 𝓘(ℂ, V.analyticModel)
        𝓘(ℂ, Z.regularAnalyticModel × (Fin p → ℂ)) ∧
      ∀ y : P.neighborhood, P.normalCoordinate y = f y.val := by
  let c := chartAt V.analyticModel (Z.regularComplementInclusion x)
  let g : V.analyticModel → (Fin p → ℂ) := fun t => f (c.symm t)
  have hgf : ContDiffAt ℂ ω g (c (Z.regularComplementInclusion x)) :=
    ComplexPoints.Analytic.ImmersionChartDerivative.contDiffAt_preferredChartMap hf
  have hd := ComplexPoints.Analytic.ImmersionChartDerivative.mfderiv_eq_preferredChartDerivative (hf.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, Fin p → ℂ) f (Z.regularComplementInclusion x) =
    fderiv ℂ g (c (Z.regularComplementInclusion x)) at hd
  have hgs : Function.Surjective (fderiv ℂ g (c (Z.regularComplementInclusion x))) :=
    (congrArg (fun L : V.analyticModel →L[ℂ] (Fin p → ℂ) => Function.Surjective L) hd).mp hs
  have hk := (fderiv ℂ g (c (Z.regularComplementInclusion x))).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hgs, finrank_top, Module.finrank_fin_fun] at hk
  have he : Module.finrank ℂ (fderiv ℂ g (c (Z.regularComplementInclusion x))).ker =
      Module.finrank ℂ Z.regularAnalyticModel := by
    have hz := Z.regularComplexDimension_add_codimension
    change p + Module.finrank ℂ (fderiv ℂ g (c (Z.regularComplementInclusion x))).ker =
      Module.finrank ℂ (Fin V.complexDimension → ℂ) at hk
    rw [Module.finrank_fin_fun] at hk
    change _ = Module.finrank ℂ (Fin Z.regularComplexDimension → ℂ)
    rw [Module.finrank_fin_fun]
    omega
  have hx : Z.regularComplementInclusion x ∈ c.source ∩ (U : Set V.analyticSpace) :=
    ⟨mem_chart_source _ _, hxU⟩
  have hgzero : ∀ y ∈ c.source ∩ (U : Set V.analyticSpace),
      y ∈ Set.range Z.regularComplementInclusion ↔ g (c y) = 0 := by
    intro y hy
    change _ ↔ f (c.symm (c y)) = 0
    rw [c.left_inv hy.1]
    exact hzero y hy.2
  obtain ⟨P, hPU, hPd, hPn⟩ := EquationNormalPair.Constructions.exists_equation_normalPair
    Z.regularComplementInclusion x c (mdifferentiable_chart _)
    (c.source ∩ (U : Set V.analyticSpace)) (c.open_source.inter U.isOpen) hx
    Set.inter_subset_left g hgf hgs hgzero (ContinuousLinearEquiv.ofFinrankEq he)
  refine ⟨P, fun _ hy => (hPU hy).2, hPd, ?_⟩
  intro y
  rw [hPn]
  change f (c.symm (c y.val)) = f y.val
  rw [c.left_inv (hPU y.property).1]

end

end OAI.AlgebraicGeometry.CycleClass.Thom.ManifoldEquationCoordinates.Constructions
