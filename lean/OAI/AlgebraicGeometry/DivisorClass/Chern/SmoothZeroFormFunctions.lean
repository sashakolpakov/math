import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultZeroKernel
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarDolbeaultProduct

/-! # Smooth Zero Form Functions -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothZeroFormFunctions

noncomputable section

/-! Every actual smooth open zero-form is its literal smooth scalar function; holomorphic multiplication commutes with its Dolbeault derivative. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {U V : Opens M}

theorem openManifoldZeroScalar_smooth (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (Manifold.DolbeaultZeroKernel.openManifoldZeroScalar a) (U : Set M) := by
  intro x hx
  let e := chartAt E x
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hex : x ∈ e.source := mem_chart_source E x
  have hy : e x ∈ Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U := Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen e U hex hx
  have hF : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (Manifold.DolbeaultZeroKernel.openManifoldZeroScalar a ∘ e.symm) (e x) :=
    ((Manifold.DolbeaultZeroKernel.openManifoldZeroScalar_chart_smooth a e he).contDiffAt
      ((Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds hy)).contMDiffAt
  have he' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hex
  apply ContMDiffAt.contMDiffWithinAt
  apply (hF.comp x he').congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hex] with z hz
  change Manifold.DolbeaultZeroKernel.openManifoldZeroScalar a z = Manifold.DolbeaultZeroKernel.openManifoldZeroScalar a (e.symm (e z))
  rw [e.left_inv hz]

def smoothManifoldZeroFunction (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) :
    SmoothScalarForm.SmoothComplexOpenFunction (E := E) U :=
  ⟨fun x => a x 0, by
    intro x
    have hc := (openManifoldZeroScalar_smooth a).contMDiffAt (U.isOpen.mem_nhds x.property)
    have ht := (contMDiffAt_subtype_iff (U := U) (x := x)).mpr hc
    simpa only [Manifold.DolbeaultZeroKernel.openManifoldZeroScalar_apply] using ht⟩

theorem smoothScalarOpenZeroForm_ofZeroFunction (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) :
    SmoothScalarForm.smoothScalarOpenZeroForm (smoothManifoldZeroFunction a) = a := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  rw [SmoothScalarForm.smoothScalarOpenZeroForm_apply]
  change a x 0 = a x v
  congr 1
  exact Subsingleton.elim _ _

theorem smoothManifoldZeroFunction_ofScalar (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    smoothManifoldZeroFunction (SmoothScalarForm.smoothScalarOpenZeroForm f) = f := by
  apply ContMDiffMap.ext
  intro x
  exact SmoothScalarForm.smoothScalarOpenZeroForm_apply f x 0

theorem smoothManifoldZeroFunction_restrict (h : V ≤ U) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) :
    smoothManifoldZeroFunction (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a) =
      SmoothScalarForm.smoothComplexOpenFunctionRestrict h (smoothManifoldZeroFunction a) := by
  apply ContMDiffMap.ext
  intro x
  rfl

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M]

theorem smoothHolomorphicScalar_dbar_mul_form (g : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := U))
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) :
    Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 (SmoothScalarForm.smoothScalarOpenFormMul (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g) a) =
      SmoothScalarForm.smoothScalarOpenFormMul (SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen g) (Open.ManifoldDolbeault.openManifoldDolbeaultD 0 0 0 a) := by
  have h := SmoothScalarDolbeaultProduct.smoothHolomorphicScalar_dbar_mul g (smoothManifoldZeroFunction a)
  rw [SmoothScalarForm.smoothScalarOpenZeroForm_mul, smoothScalarOpenZeroForm_ofZeroFunction] at h
  exact h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothZeroFormFunctions
