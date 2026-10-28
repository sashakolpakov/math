import OAI.NumberTheory.Quaternion.Arithmetic.CurveTangentRestriction
import Mathlib.Topology.Constructions

/-! # Product Curve Tangents -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.ProductCurveTangents

noncomputable section

/-! Simultaneous local curves give a tangent direction over a common
scalar field even when the local norms have different normalizations. -/

open Set Filter _root_.Topology

theorem product_curve_derivatives_mem_tangentCone
    {κ ι : Type*} {K A : ι → Type*} [NontriviallyNormedField κ]
    [∀ i, NontriviallyNormedField (K i)] [∀ i, Algebra κ (K i)]
    [∀ i, NormedAddCommGroup (A i)] [∀ i, NormedSpace (K i) (A i)]
    [∀ i, Module κ (A i)] [∀ i, IsScalarTower κ (K i) (A i)]
    (he : ∀ i, Continuous (algebraMap κ (K i)))
    (f : ∀ i, K i → A i) (y : ∀ i, A i) (hf : ∀ i, HasDerivAt (f i) (y i) 0)
    {s : Set (∀ i, A i)} (hs : ∀ᶠ t in 𝓝 (0 : ∀ i, K i), (fun i => f i (t i)) ∈ s) :
    y ∈ tangentConeAt κ s (fun i => f i 0) := by
  have he₀ (i : ι) : Tendsto (algebraMap κ (K i)) (𝓝[≠] (0 : κ)) (𝓝 (0 : K i)) := by
    simpa only [map_zero] using
      ((he i).continuousAt (x := (0 : κ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := ({0}ᶜ : Set κ)))
  have hp : Tendsto (fun t : κ => fun i => algebraMap κ (K i) t)
      (𝓝[≠] 0) (𝓝 (0 : ∀ i, K i)) := tendsto_pi_nhds.mpr he₀
  have hd : Tendsto (fun t : κ => fun i => f i (algebraMap κ (K i) t) - f i 0)
      (𝓝[≠] 0) (𝓝 (0 : ∀ i, A i)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simpa only [sub_self, Function.comp_def, Pi.zero_apply] using
      ((hf i).continuousAt.tendsto.comp (he₀ i)).sub (tendsto_const_nhds (x := f i 0))
  apply mem_tangentConeAt_of_seq (𝓝[≠] (0 : κ)) (fun t => t⁻¹)
    (fun t => fun i => f i (algebraMap κ (K i) t) - f i 0) hd
  · filter_upwards [hp hs] with t ht
    change (fun i => f i (algebraMap κ (K i) t)) ∈ s at ht
    convert ht using 1
    ext i
    change f i 0 + (f i (algebraMap κ (K i) t) - f i 0) = f i (algebraMap κ (K i) t)
    abel
  · exact tendsto_pi_nhds.mpr (fun i => CurveTangentRestriction.curve_slope_restrictScalars_tendsto (he i) (hf i))

end

end OAI.NumberTheory.Quaternion.Arithmetic.ProductCurveTangents
