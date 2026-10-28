import Mathlib.Topology.Continuous
import Mathlib.Topology.NhdsWithin

/-! # Dense Parameter Closure -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.DenseParameterClosure

noncomputable section

/-! A curve evaluated on a dense parameter set lies in a closed set
wherever it is continuous and all sufficiently near dense parameters
have values in that set. -/

open Set Filter _root_.Topology

theorem dense_parameters_mem_closed {R X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {d : R → X} (hd : DenseRange d) {f : X → Y} {C : Set Y} (hC : IsClosed C)
    {x : X} (hf : ContinuousAt f x) {U : Set X} (hU : U ∈ 𝓝 x)
    (hvalues : ∀ r, d r ∈ U → f (d r) ∈ C) : f x ∈ C := by
  let : NeBot (𝓝[range d] x) := hd.nhdsWithin_neBot x
  have hlim : Tendsto f (𝓝[range d] x) (𝓝 (f x)) :=
    hf.tendsto.mono_left nhdsWithin_le_nhds
  apply hC.mem_of_tendsto hlim
  filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with y hy hr
  obtain ⟨r, rfl⟩ := hr
  exact hvalues r hy

end

end OAI.NumberTheory.Quaternion.Arithmetic.DenseParameterClosure
