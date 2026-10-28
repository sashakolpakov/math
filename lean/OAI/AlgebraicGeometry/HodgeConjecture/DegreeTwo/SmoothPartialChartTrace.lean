import OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTraceDimension
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-! # Smooth Partial Chart Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothPartialChartTrace.Constructions

noncomputable section

/-! The actual compact trace is preserved by smooth complex partial charts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicTopology.Duality.Poincare.ComplexManifoldTraceDimension
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
variable [T2Space M] [T2Space N] [ChartedSpace (Fin p → ℂ) M] [ChartedSpace (Fin p → ℂ) N]
variable [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 N]
variable (e : OpenPartialHomeomorph M N)

abbrev partialChartSourceOpen : Opens M := ⟨e.source,e.open_source⟩

abbrev partialChartTargetOpen : Opens N := ⟨e.target,e.open_target⟩

abbrev partialChartHomeomorph : partialChartSourceOpen e ≃ₜ partialChartTargetOpen e :=
  e.toHomeomorphSourceTarget

theorem partialChartHomeomorph_contMDiff
    (he : ContMDiffOn 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) ∞ e e.source) :
    ContMDiff 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) ∞ (partialChartHomeomorph e) := by
  let _ := (inferInstance : T2Space M)
  let _ := (inferInstance : T2Space N)
  let _ := (inferInstance : IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M)
  let _ := (inferInstance : IsManifold 𝓘(ℂ, Fin p → ℂ) 1 N)
  apply (ContMDiff.subtypeVal_comp_iff
    (partialChartTargetOpen e) (partialChartHomeomorph e)).mp
  intro x
  have hx := (he x.val x.property).contMDiffAt (e.open_source.mem_nhds x.property)
  exact hx.comp x contMDiff_subtype_val.contMDiffAt

theorem partialChartHomeomorph_symm_contMDiff
    (he : ContMDiffOn 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) ∞ e.symm e.target) :
    ContMDiff 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) ∞ (partialChartHomeomorph e).symm := by
  let _ := (inferInstance : T2Space M)
  let _ := (inferInstance : T2Space N)
  let _ := (inferInstance : IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M)
  let _ := (inferInstance : IsManifold 𝓘(ℂ, Fin p → ℂ) 1 N)
  apply (ContMDiff.subtypeVal_comp_iff
    (partialChartSourceOpen e) (partialChartHomeomorph e).symm).mp
  intro x
  have hx := (he x.val x.property).contMDiffAt (e.open_target.mem_nhds x.property)
  exact hx.comp x contMDiff_subtype_val.contMDiffAt

theorem complexManifoldTrace_partialChart
    (he : ContMDiffOn 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) ∞ e.symm e.target) :
    (AlgebraicTopology.Duality.Poincare.CompactSupportHomeomorph.compactSupportedCohomologyHomeomorphIso (ModuleCat.of ℚ ℚ)
      (X := TopCat.of (partialChartSourceOpen e)) (Y := TopCat.of (partialChartTargetOpen e))
      (partialChartHomeomorph e) (2*p)).hom ≫
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace p (M := partialChartSourceOpen e) =
      AlgebraicTopology.Duality.Poincare.ComplexManifoldTrace.complexManifoldTrace p (M := partialChartTargetOpen e) :=
  AlgebraicTopology.Duality.Poincare.ComplexManifoldTraceDimension.complexManifoldTrace_homeomorphIso p (partialChartHomeomorph e)
    ((partialChartHomeomorph_contMDiff e he).of_le (by simp))
    ((partialChartHomeomorph_symm_contMDiff e hei).of_le (by simp))

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SmoothPartialChartTrace.Constructions
