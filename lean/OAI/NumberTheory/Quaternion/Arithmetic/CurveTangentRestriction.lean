import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.Basic

/-! # Curve Tangent Restriction -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.CurveTangentRestriction

noncomputable section

/-! A differentiable local curve supplies tangent directions over
any continuously embedded nontrivially normed scalar subfield.
No equality between the two fields' norm normalizations is required. -/

open Set Filter _root_.Topology

theorem curve_slope_restrictScalars_tendsto
    {κ K A : Type*} [NontriviallyNormedField κ] [NontriviallyNormedField K]
    [Algebra κ K] [NormedAddCommGroup A] [NormedSpace K A] [Module κ A]
    [IsScalarTower κ K A] (he : Continuous (algebraMap κ K))
    {f : K → A} {y : A} (hf : HasDerivAt f y 0) :
    Tendsto (fun t : κ => t⁻¹ • (f (algebraMap κ K t) - f 0)) (𝓝[≠] 0) (𝓝 y) := by
  have he₀ : Tendsto (algebraMap κ K) (𝓝[≠] (0 : κ)) (𝓝 (0 : K)) := by
    simpa only [map_zero] using
      (he.continuousAt (x := (0 : κ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := ({0}ᶜ : Set κ)))
  have he' : Tendsto (algebraMap κ K) (𝓝[≠] (0 : κ)) (𝓝[≠] (0 : K)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨he₀, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (map_ne_zero (algebraMap κ K)).mpr ht
  have hlim := hf.tendsto_slope.comp he'
  have heq : (fun t : κ => t⁻¹ • (f (algebraMap κ K t) - f 0)) =
      (slope f 0 ∘ algebraMap κ K) := by
    funext t
    simp only [Function.comp_apply, slope, sub_zero]
    rw [← map_inv₀]
    exact (IsScalarTower.algebraMap_smul K t⁻¹ _).symm
  exact heq.symm ▸ hlim

theorem curve_derivative_mem_tangentCone_restrictScalars
    {κ K A : Type*} [NontriviallyNormedField κ] [NontriviallyNormedField K]
    [Algebra κ K] [NormedAddCommGroup A] [NormedSpace K A] [Module κ A]
    [IsScalarTower κ K A] (he : Continuous (algebraMap κ K))
    {f : K → A} {y : A} (hf : HasDerivAt f y 0) {s : Set A}
    (hs : ∀ᶠ t in 𝓝 (0 : K), f t ∈ s) : y ∈ tangentConeAt κ s (f 0) := by
  have he₀ : Tendsto (algebraMap κ K) (𝓝[≠] (0 : κ)) (𝓝 (0 : K)) := by
    simpa only [map_zero] using
      (he.continuousAt (x := (0 : κ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := ({0}ᶜ : Set κ)))
  have hd : Tendsto (fun t : κ => f (algebraMap κ K t) - f 0) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [sub_self, Function.comp_def] using
      (hf.continuousAt.tendsto.comp he₀).sub (tendsto_const_nhds (x := f 0))
  apply mem_tangentConeAt_of_seq (𝓝[≠] (0 : κ)) (fun t => t⁻¹)
    (fun t => f (algebraMap κ K t) - f 0) hd
  · filter_upwards [he₀ hs] with t ht
    change f (algebraMap κ K t) ∈ s at ht
    simpa only [← add_sub_assoc, add_sub_cancel_left] using ht
  · exact curve_slope_restrictScalars_tendsto he hf

end

end OAI.NumberTheory.Quaternion.Arithmetic.CurveTangentRestriction
