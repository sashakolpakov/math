import OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.Differential
import OAI.AlgebraicGeometry.CycleClass.Thom.LinearNormalExactness

/-! # Tangent Kernel -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.CycleClass.Thom.NormalPair.TangentKernel.Constructions

/-! The kernel of the actual normal differential is the actual immersion tangent space. -/

open scoped _root_.Manifold _root_.Topology

set_option backward.isDefEq.respectTransparency false

variable {M N E F G : Type} [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E M]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)

def ambientNormal (y : N) : F := (P.ambientChart y).2

omit [TopologicalSpace M] [ChartedSpace E M] in
theorem ambientNormal_mfderiv
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × F)) :
    mfderiv 𝓘(ℂ, G) 𝓘(ℂ, F) (ambientNormal P) (f x) =
      (ContinuousLinearMap.snd ℂ E F).comp
        (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, E × F) P.ambientChart (f x)) :=
  ((ContinuousLinearMap.snd ℂ E F).hasMFDerivAt.comp (f x)
    (hP.mdifferentiableAt P.point_mem_source).hasMFDerivAt).mfderiv

omit [TopologicalSpace M] [ChartedSpace E M] in
theorem ambientNormal_submersion
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × F)) :
    Function.Surjective (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, F) (ambientNormal P) (f x)) := by
  rw [ambientNormal_mfderiv P hP]
  exact (show Function.Surjective (ContinuousLinearMap.snd ℂ E F) from
    fun z => ⟨(0, z), rfl⟩).comp (hP.mfderiv_bijective P.point_mem_source).2

theorem ambientNormal_comp_mfderiv_zero
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × F))
    (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, G) f x) :
    (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, F) (ambientNormal P) (f x)).comp
      (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) f x) = 0 := by
  have he : (ambientNormal P ∘ f) =ᶠ[𝓝 x] (fun _ : M => (0 : F)) := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds
      (P.isOpen_neighborhood.mem_nhds P.point_mem_neighborhood)] with y hy
    exact (P.range_iff (f y) hy).mp ⟨y, rfl⟩
  have hd : MDifferentiableAt 𝓘(ℂ, G) 𝓘(ℂ, F) (ambientNormal P) (f x) :=
    (ContinuousLinearMap.snd ℂ E F).mdifferentiableAt.comp (f x)
      (hP.mdifferentiableAt P.point_mem_source)
  have hz := he.mfderiv_eq (I := 𝓘(ℂ, E)) (I' := 𝓘(ℂ, F))
  rw [mfderiv_comp x hd hf, mfderiv_const] at hz
  exact hz

theorem ambientNormal_ker [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    [FiniteDimensional ℂ G]
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × F))
    (hf : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, G) f x)
    (hi : Function.Injective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) f x)) :
    LinearMap.ker (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, F) (ambientNormal P) (f x)).toLinearMap =
      LinearMap.range (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, G) f x).toLinearMap := by
  apply LinearNormalExactness.Constructions.ker_eq_range (k := ℂ) (W := E) (A := G) (V := F)
    _ _ hi (ambientNormal_submersion P hP)
  · exact congrArg ContinuousLinearMap.toLinearMap (ambientNormal_comp_mfderiv_zero P hP hf)
  · have hd := (hP.mfderiv P.point_mem_source).toLinearEquiv.finrank_eq
    change Module.finrank ℂ G = Module.finrank ℂ (E × F) at hd
    rw [Module.finrank_prod] at hd
    exact hd.symm

end AlgebraicGeometry.CycleClass.Thom.NormalPair.TangentKernel.Constructions

namespace AlgebraicGeometry.CycleClass.Thom.NormalPair.TangentKernel.Constructions.Map

/-! Maps landing in the actual immersion image have zero normal differential. -/

open scoped _root_.Manifold _root_.Topology

open OAI.AlgebraicGeometry.CycleClass.Thom.NormalPair.TangentKernel.Constructions

variable {M L N E F G H : Type} [TopologicalSpace L] [TopologicalSpace N]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [ChartedSpace G N]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [ChartedSpace H L]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E F f x)

theorem normal_comp_zero_of_range (g : L → N) (y : L)
    (hP : P.ambientChart.MDifferentiable 𝓘(ℂ, G) 𝓘(ℂ, E × F))
    (hg : MDifferentiableAt 𝓘(ℂ, H) 𝓘(ℂ, G) g y)
    (hy : g y = f x) (hr : Set.range g ⊆ Set.range f) :
    (mfderiv 𝓘(ℂ, G) 𝓘(ℂ, F) (ambientNormal P) (f x)).comp
      (mfderiv 𝓘(ℂ, H) 𝓘(ℂ, G) g y) = 0 := by
  have hyn : g y ∈ P.neighborhood := hy.symm ▸ P.point_mem_neighborhood
  have he : (ambientNormal P ∘ g) =ᶠ[𝓝 y] (fun _ : L => (0 : F)) := by
    filter_upwards [hg.continuousAt.preimage_mem_nhds
      (P.isOpen_neighborhood.mem_nhds hyn)] with z hz
    exact (P.range_iff (g z) hz).mp (hr ⟨z, rfl⟩)
  have hd : MDifferentiableAt 𝓘(ℂ, G) 𝓘(ℂ, F) (ambientNormal P) (g y) := by
    rw [hy]
    exact (ContinuousLinearMap.snd ℂ E F).mdifferentiableAt.comp (f x)
      (hP.mdifferentiableAt P.point_mem_source)
  have hz := he.mfderiv_eq (I := 𝓘(ℂ, H)) (I' := 𝓘(ℂ, F))
  rw [mfderiv_comp y hd hg, mfderiv_const, hy] at hz
  exact hz

end AlgebraicGeometry.CycleClass.Thom.NormalPair.TangentKernel.Constructions.Map

end

end OAI
