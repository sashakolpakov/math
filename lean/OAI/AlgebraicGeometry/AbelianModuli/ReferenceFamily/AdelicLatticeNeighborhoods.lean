import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicNeighborhoods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicCoefficientTopology
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Adelic Lattice Neighborhoods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicLatticeNeighborhoods

noncomputable section

/-! Integer multiples uniformly shrink finite families of integral
adele coefficients and finitely generated completed lattices. -/

open scoped Classical _root_.Topology

theorem finite_adele_pi_integer_multiple_small {I : Type*}
    (U : Set (I → AdelicData.RationalFiniteAdeles)) (hU : U ∈ 𝓝 (0 : I → AdelicData.RationalFiniteAdeles)) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ a : I → AdelicData.RationalFiniteAdeles,
      (∀ i, a i ∈ AdelicData.integralFiniteAdeles) → n • a ∈ U := by
  rw [nhds_pi] at hU
  obtain ⟨J, W, hW, hsub⟩ := Filter.mem_pi'.mp hU
  choose n hn hsmall using fun i => AdelicNeighborhoods.finite_adele_integer_multiple_small (W i) (hW i)
  refine ⟨∏ i ∈ J, n i, Finset.prod_ne_zero_iff.mpr (fun i _ => hn i), ?_⟩
  intro a ha
  apply hsub
  intro i hi
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n hi
  change (∏ i ∈ J, n i) • a i ∈ W i
  rw [hc, mul_smul]
  exact hsmall i (c • a i) (AdelicData.integralFiniteAdeles.zsmul_mem (ha i) c)

variable {W : Type*} [AddCommGroup W] [Module AdelicData.RationalFiniteAdeles W]
  [Module AdelicData.integralFiniteAdeles W] [IsScalarTower AdelicData.integralFiniteAdeles AdelicData.RationalFiniteAdeles W]
  [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul AdelicData.RationalFiniteAdeles W]

/-- A fixed integer simultaneously shrinks every point of a finitely
generated completed lattice into a prescribed zero-neighborhood. -/
theorem completed_lattice_integer_multiple_small (L : Submodule AdelicData.integralFiniteAdeles W)
    (hL : L.FG) (U : Set W) (hU : U ∈ 𝓝 (0 : W)) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ L, n • x ∈ U := by
  obtain ⟨s, hs⟩ := hL
  let f : (s → AdelicData.RationalFiniteAdeles) → W := fun c => ∑ i, c i • (i.val : W)
  have hf : Continuous f := by
    apply continuous_finsetSum
    intro i _
    exact (continuous_apply i).smul continuous_const
  have hf0 : f 0 = 0 := by simp only [f, Pi.zero_apply, zero_smul, Finset.sum_const_zero]
  have hpre : f ⁻¹' U ∈ 𝓝 (0 : s → AdelicData.RationalFiniteAdeles) := by
    have hUF : U ∈ 𝓝 (f 0) := hf0.symm ▸ hU
    exact hf.continuousAt.preimage_mem_nhds hUF
  obtain ⟨n, hn, hsmall⟩ := finite_adele_pi_integer_multiple_small (f ⁻¹' U) hpre
  refine ⟨n, hn, ?_⟩
  intro x hx
  have hx' : x ∈ Submodule.span AdelicData.integralFiniteAdeles (s : Set W) := hs.symm ▸ hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_finset'.mp hx'
  let a : s → AdelicData.RationalFiniteAdeles := fun i => c i
  have ha := hsmall a (fun i => (c i).property)
  have hrepr : f a = x := by
    change (∑ i : s, (c i : AdelicData.RationalFiniteAdeles) • (i.val : W)) = x
    have ht (i : s) : (c i : AdelicData.RationalFiniteAdeles) • (i.val : W) = c i • (i.val : W) :=
      IsScalarTower.algebraMap_smul AdelicData.RationalFiniteAdeles (c i) (i.val : W)
    exact (Finset.sum_congr rfl (fun i _ => ht i)).trans hc
  have he : f (n • a) = n • x := by
    change (∑ i, (n • a i) • (i.val : W)) = n • x
    rw [← hrepr]
    change (∑ i, (n • a i) • (i.val : W)) = n • (∑ i, a i • (i.val : W))
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_assoc n (a i) (i.val : W)
  exact he ▸ ha

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AdelicLatticeNeighborhoods
