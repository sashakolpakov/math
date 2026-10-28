import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ImmersionFactorAt
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts

/-! # Manifold Projective -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.ManifoldProjective.Constructions.ManifoldImmersionFactor

/-! # RiemannProjectivity: detecting holomorphic maps in ambient immersion coordinates -/

open Set Filter ChartedSpace
open scoped _root_.Topology _root_.Manifold

variable {V W Z N : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z] [FiniteDimensional ℂ Z]
  [TopologicalSpace N] [ChartedSpace W N] [IsManifold (𝓘(ℂ, W)) 1 N]

theorem from_normedSpace {g : V → N} {f : N → Z} {x : V} {U : Set N}
    (hU : IsOpen U) (hx : g x ∈ U)
    (hf : MDifferentiableOn (𝓘(ℂ, W)) (𝓘(ℂ, Z)) f U)
    (hi : Function.Injective (mfderiv (𝓘(ℂ, W)) (𝓘(ℂ, Z)) f (g x)))
    (hg : ContinuousAt g x) (hc : DifferentiableAt ℂ (f ∘ g) x) :
    MDifferentiableAt (𝓘(ℂ, V)) (𝓘(ℂ, W)) g x := by
  let e := chartAt W (g x)
  let B := e.target ∩ e.symm ⁻¹' U
  let F : W → Z := f ∘ e.symm
  have he : e.MDifferentiable (𝓘(ℂ, W)) (𝓘(ℂ, W)) := mdifferentiable_chart (g x)
  have hxe : g x ∈ e.source := mem_chart_source W (g x)
  have hz : e (g x) ∈ B := ⟨e.map_source hxe, by simpa only [mem_preimage, e.left_inv hxe] using hx⟩
  have hB : IsOpen B := e.isOpen_inter_preimage_symm hU
  have hF : DifferentiableOn ℂ F B := by
    intro z hz
    exact (((hf (e.symm z) hz.2).mdifferentiableAt (hU.mem_nhds hz.2)).comp z
      (he.mdifferentiableAt_symm hz.1)).differentiableAt.differentiableWithinAt
  have hFi : Function.Injective (fderiv ℂ F (e (g x))) := by
    rw [← mfderiv_eq_fderiv]
    change Function.Injective (mfderiv (𝓘(ℂ, W)) (𝓘(ℂ, Z)) (f ∘ e.symm) (e (g x)))
    have hfe : MDifferentiableAt (𝓘(ℂ, W)) (𝓘(ℂ, Z)) f (e.symm (e (g x))) := by
      rw [e.left_inv hxe]
      exact (hf (g x) hx).mdifferentiableAt (hU.mem_nhds hx)
    rw [mfderiv_comp _ hfe (he.mdifferentiableAt_symm hz.1)]
    have hfi : Function.Injective (mfderiv (𝓘(ℂ, W)) (𝓘(ℂ, Z)) f (e.symm (e (g x)))) := by
      rw [e.left_inv hxe]
      exact hi
    exact hfi.comp (he.symm.mfderiv_injective hz.1)
  have heg : ContinuousAt (e ∘ g) x := (e.continuousAt hxe).comp hg
  have hFeg : DifferentiableAt ℂ (F ∘ (e ∘ g)) x := by
    apply hc.congr_of_eventuallyEq
    filter_upwards [hg.preimage_mem_nhds (e.open_source.mem_nhds hxe)] with y hy
    change f (e.symm (e (g y))) = f (g y)
    rw [e.left_inv hy]
  have hd := ImmersionFactorAt.Constructions.ImmersionFactor.differentiableAt_of_comp (g := e ∘ g) (x := x) hB hz hF hFi heg hFeg
  apply mdifferentiableAt_iff_target.mpr
  refine ⟨hg, ?_⟩
  exact hd.mdifferentiableAt

variable {M : Type*} [TopologicalSpace M] [ChartedSpace V M] [IsManifold (𝓘(ℂ, V)) 1 M]

theorem mdifferentiableAt_of_comp {g : M → N} {f : N → Z} {x : M} {U : Set N}
    (hU : IsOpen U) (hx : g x ∈ U)
    (hf : MDifferentiableOn (𝓘(ℂ, W)) (𝓘(ℂ, Z)) f U)
    (hi : Function.Injective (mfderiv (𝓘(ℂ, W)) (𝓘(ℂ, Z)) f (g x)))
    (hg : ContinuousAt g x)
    (hc : MDifferentiableAt (𝓘(ℂ, V)) (𝓘(ℂ, Z)) (f ∘ g) x) :
    MDifferentiableAt (𝓘(ℂ, V)) (𝓘(ℂ, W)) g x := by
  let e := chartAt V x
  have hxe : x ∈ e.source := mem_chart_source V x
  have he : e.MDifferentiable (𝓘(ℂ, V)) (𝓘(ℂ, V)) := mdifferentiable_chart x
  have hge : ContinuousAt (g ∘ e.symm) (e x) := by
    apply ContinuousAt.comp _ (e.continuousAt_symm (e.map_source hxe))
    simpa only [e.left_inv hxe] using hg
  have hce : DifferentiableAt ℂ (f ∘ (g ∘ e.symm)) (e x) := by
    have h := hc.comp_of_eq (e x) (he.mdifferentiableAt_symm (e.map_source hxe)) (e.left_inv hxe)
    exact h.differentiableAt
  have hxeU : g (e.symm (e x)) ∈ U := by simpa only [e.left_inv hxe] using hx
  have hie : Function.Injective
      (mfderiv (𝓘(ℂ, W)) (𝓘(ℂ, Z)) f (g (e.symm (e x)))) := by
    rw [e.left_inv hxe]
    exact hi
  have hd := from_normedSpace (g := g ∘ e.symm) (x := e x) hU hxeU hf hie hge hce
  apply (mdifferentiableAt_iff_source_of_mem_source (x := x) hxe).mpr
  exact hd.mdifferentiableWithinAt

end Geometry.ComplexTorus.RiemannProjectivity.ManifoldProjective.Constructions.ManifoldImmersionFactor

namespace Geometry.ComplexTorus.RiemannProjectivity.ManifoldProjective.Constructions.ProjectiveManifoldComparison

/-! # RiemannProjectivity: a common projective immersion identifies complex manifold structures -/

open Set
open scoped _root_.Manifold
open OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts

variable {V W M N : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  [TopologicalSpace M] [ChartedSpace V M] [IsManifold (𝓘(ℂ, V)) 1 M]
  [TopologicalSpace N] [ChartedSpace W N] [IsManifold (𝓘(ℂ, W)) 1 N]
  {n : ℕ}

theorem mdifferentiable_of_common_embedding
    (f : M → Projectivization ℂ (Fin (n + 1) → ℂ))
    (g : N → Projectivization ℂ (Fin (n + 1) → ℂ)) (hg : Continuous g)
    (e : M → N) (he : Continuous e) (hcomm : ∀ x, g (e x) = f x)
    (hf : ∀ i x, f x ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      MDifferentiableAt (𝓘(ℂ, V)) (𝓘(ℂ, Fin n → ℂ)) (fun y => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f y)) x)
    (hd : ∀ i x, g x ∈ (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).source →
      MDifferentiableAt (𝓘(ℂ, W)) (𝓘(ℂ, Fin n → ℂ)) (fun y => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g y)) x ∧
      Function.Injective (mfderiv (𝓘(ℂ, W)) (𝓘(ℂ, Fin n → ℂ))
        (fun y => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g y)) x)) :
    MDifferentiable (𝓘(ℂ, V)) (𝓘(ℂ, W)) e := by
  intro x
  obtain ⟨i, hi⟩ := AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.exists_mem_projectiveFinChart_source (g (e x))
  have hcomp : MDifferentiableAt (𝓘(ℂ, V)) (𝓘(ℂ, Fin n → ℂ))
      ((fun y => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g y)) ∘ e) x := by
    have hfun : ((fun y => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (g y)) ∘ e) =
        (fun y => AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i (f y)) := funext (fun y => congrArg (AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i) (hcomm y))
    rw [hfun]
    exact hf i x (hcomm x ▸ hi)
  exact ManifoldImmersionFactor.mdifferentiableAt_of_comp
    ((AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveCharts.projectiveFinChart i).open_source.preimage hg) hi
    (fun y hy => (hd i y hy).1.mdifferentiableWithinAt) (hd i (e x) hi).2
    he.continuousAt hcomp

end Geometry.ComplexTorus.RiemannProjectivity.ManifoldProjective.Constructions.ProjectiveManifoldComparison

end

end OAI
