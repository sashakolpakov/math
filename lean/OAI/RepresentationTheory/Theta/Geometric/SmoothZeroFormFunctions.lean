import OAI.RepresentationTheory.Theta.Geometric.SmoothSheaf
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm
import OAI.AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultZeroKernel

/-! # Smooth Zero Form Functions -/

namespace OAI.RepresentationTheory.Theta.Geometric.SmoothZeroFormFunctions

noncomputable section

/-! Actual smooth scalar functions and smooth zero-forms on manifold
opens are equivalent by evaluation at the unique empty tangent tuple. -/

set_option backward.isDefEq.respectTransparency false
open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem openZeroFormScalar_contMDiffOn {U : Opens M} (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultZeroKernel.openManifoldZeroScalar a) (U : Set M) := by
  intro x hx
  let e := chartAt E x
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hex : x ∈ e.source := mem_chart_source E x
  have hy : e x ∈ Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U := Analysis.DifferentialForms.Manifold.ChartEquiv.mem_chartImageOpen e U hex hx
  have hF : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultZeroKernel.openManifoldZeroScalar a ∘ e.symm) (e x) :=
    ((AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultZeroKernel.openManifoldZeroScalar_chart_smooth a e he).contDiffAt
      ((Analysis.DifferentialForms.Manifold.ChartEquiv.chartImageOpen e U).isOpen.mem_nhds hy)).contMDiffAt
  have he' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas he) hex
  apply ContMDiffAt.contMDiffWithinAt
  apply (hF.comp x he').congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hex] with y hy
  change AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultZeroKernel.openManifoldZeroScalar a y = AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultZeroKernel.openManifoldZeroScalar a (e.symm (e y))
  rw [e.left_inv hy]

def smoothZeroFormScalar {U : Opens M} (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) : SmoothCocyclePrimitive.SmoothOpenScalar E U where
  val x := AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultZeroKernel.openManifoldZeroScalar a x.val
  property := by
    intro x
    apply (contMDiffAt_subtype_iff (U := U) (x := x)).mpr
    exact (openZeroFormScalar_contMDiffOn a).contMDiffAt (U.isOpen.mem_nhds x.property)

theorem smoothZeroFormScalar_apply {U : Opens M} (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) (x : U) :
    smoothZeroFormScalar a x = a x 0 := AlgebraicGeometry.DivisorClass.Chern.Manifold.DolbeaultZeroKernel.openManifoldZeroScalar_apply a x

theorem smoothScalarOpenZeroForm_bijective (U : Opens M) :
    Function.Bijective (AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm.smoothScalarOpenZeroFormLinear (E := E) U) := by
  constructor
  · intro f g h
    apply ContMDiffMap.ext
    intro x
    have H := congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0 => a x 0) h
    change AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm.smoothScalarOpenZeroForm f x 0 = AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm.smoothScalarOpenZeroForm g x 0 at H
    simpa only [AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm.smoothScalarOpenZeroForm_apply] using H
  · intro a
    refine ⟨smoothZeroFormScalar a, ?_⟩
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    change AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm.smoothScalarOpenZeroForm (smoothZeroFormScalar a) x v = a x v
    rw [AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm.smoothScalarOpenZeroForm_apply, smoothZeroFormScalar_apply]
    exact congrArg (a x) (Subsingleton.elim 0 v)

def smoothOpenZeroFormEquiv (U : Opens M) :
    SmoothCocyclePrimitive.SmoothOpenScalar E U ≃ₗ[ℝ] Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0 :=
  LinearEquiv.ofBijective (AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm.smoothScalarOpenZeroFormLinear U) (smoothScalarOpenZeroForm_bijective U)

theorem smoothOpenZeroFormEquiv_apply (U : Opens M) (f : SmoothCocyclePrimitive.SmoothOpenScalar E U) :
    smoothOpenZeroFormEquiv U f = AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm.smoothScalarOpenZeroForm f := rfl

end

end OAI.RepresentationTheory.Theta.Geometric.SmoothZeroFormFunctions
