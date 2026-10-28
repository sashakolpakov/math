import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF
import OAI.Geometry.ComplexTorus.RiemannProjectivity.FiniteBranchesAt
import OAI.Geometry.ComplexTorus.RiemannProjectivity.GenericProjectionOn
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Regular Zero -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.RegularZero.Constructions.RegularZeroDimension

noncomputable section

/-!
# RiemannProjectivity: local dimension of regular holomorphic zero sets

Implicit-function coordinates identify a regular zero set with a complex
hyperplane. Its local Hausdorff dimension is bounded by the real dimension
of the derivative's kernel.
-/

open Set Filter _root_.Module
open scoped _root_.Topology ContDiff ENNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem local_regular_zero_dimension {f : V → ℂ} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : V} (hx : x ∈ U)
    (hdf : Function.Surjective (fderiv ℂ f x)) :
    ∃ O : Set V, IsOpen O ∧ x ∈ O ∧
      dimH (O ∩ {y | f y = 0}) ≤ (finrank ℝ (fderiv ℂ f x).ker : ℝ≥0∞) := by
  let : CompleteSpace V := FiniteDimensional.complete ℂ V
  let d := fderiv ℂ f x
  have hds : d.range = ⊤ := LinearMap.range_eq_top.mpr hdf
  have hc := HolomorphicRegularityAt.Constructions.HolomorphicRegularity.contDiffAt_one_of_differentiableOn hU hf hx
  have hs := hc.hasStrictFDerivAt (by norm_num)
  let hk := d.ker_closedComplemented_of_finiteDimensional_range
  let φ := hs.implicitFunctionDataOfComplemented f d hds hk
  have hφ : DifferentiableOn ℂ φ.prodFun U := by
    have hp : Differentiable ℂ (fun y => (Classical.choose hk) (y - x)) :=
      (Classical.choose hk).differentiable.comp (differentiable_id.sub_const x)
    exact hf.prodMk hp.differentiableOn
  have hφbij : Function.Bijective (fderiv ℂ φ.prodFun x) := by
    change Function.Bijective (fderiv ℂ φ.prodFun φ.pt)
    rw [φ.hasStrictFDerivAt.hasFDerivAt.fderiv]
    exact (φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv
      φ.range_leftDeriv φ.range_rightDeriv φ.isCompl_ker).bijective
  obtain ⟨q, hqx, hqφ, hqi⟩ := FiniteBranchesAt.Constructions.FiniteBranches.holomorphic_local_inverse hU hφ hx hφbij
  have hqfirst (y : V) : (q y).1 = f y := by rw [congrFun hqφ y]; rfl
  let A : Set d.ker := (fun u : d.ker => ((0 : ℂ), u)) ⁻¹' q.target
  let b : d.ker → V := fun u => q.symm (0, u)
  have hA : IsOpen A := q.open_target.preimage (continuous_const.prodMk continuous_id)
  have hb : DifferentiableOn ℂ b A :=
    hqi.comp ((differentiable_const (0 : ℂ)).prodMk differentiable_id).differentiableOn
      (mapsTo_preimage (fun u : d.ker => ((0 : ℂ), u)) q.target)
  have heq : q.source ∩ {y | f y = 0} = b '' A := by
    ext y
    constructor
    · rintro ⟨hy, hfy⟩
      have hqy : (0, (q y).2) = q y := Prod.ext (by rw [hqfirst, hfy]) rfl
      refine ⟨(q y).2, ?_, ?_⟩
      · change (0, (q y).2) ∈ q.target
        rw [hqy]
        exact q.map_source hy
      · change q.symm (0, (q y).2) = y
        rw [hqy, q.left_inv hy]
    · rintro ⟨u, hu, rfl⟩
      have hq : q (q.symm (0, u)) = (0, u) := q.right_inv hu
      refine ⟨q.map_target hu, ?_⟩
      exact (hqfirst _).symm.trans (congrArg Prod.fst hq)
  refine ⟨q.source, q.open_source, hqx, ?_⟩
  rw [heq]
  exact GenericProjectionOn.Constructions.GenericProjection.dimH_image_le_of_holomorphic hA hb

theorem real_kernel_dimension (d : V →L[ℂ] ℂ) (hd : Function.Surjective d) :
    finrank ℝ d.ker = finrank ℝ V - 2 := by
  have hc := d.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hd, finrank_top, finrank_self] at hc
  have hV : finrank ℝ V = 2 * finrank ℂ V := by
    rw [← Module.finrank_mul_finrank ℝ ℂ V, Complex.finrank_real_complex]
  have hK : finrank ℝ d.ker = 2 * finrank ℂ d.ker := by
    rw [← Module.finrank_mul_finrank ℝ ℂ d.ker, Complex.finrank_real_complex]
  omega

/-- The full regular part of a holomorphic zero set has real Hausdorff
dimension at most two less than the ambient real dimension. -/
theorem regular_zero_dimension {f : V → ℂ} {U : Set V}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    dimH {x | x ∈ U ∧ f x = 0 ∧ Function.Surjective (fderiv ℂ f x)} ≤
      ((finrank ℝ V - 2 : ℕ) : ℝ≥0∞) := by
  let : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
  let : SecondCountableTopology V := inferInstance
  let S := {x | x ∈ U ∧ f x = 0 ∧ Function.Surjective (fderiv ℂ f x)}
  change dimH S ≤ _
  by_contra h
  obtain ⟨x, hx, hlocal⟩ := exists_mem_nhdsWithin_lt_dimH_of_lt_dimH (lt_of_not_ge h)
  obtain ⟨O, hO, hxO, hdim⟩ := local_regular_zero_dimension hU hf hx.1 hx.2.2
  have hOS : O ∩ S ∈ 𝓝[S] x :=
    inter_mem (mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hxO)) self_mem_nhdsWithin
  have hsub : O ∩ S ⊆ O ∩ {y | f y = 0} := fun y hy => ⟨hy.1, hy.2.2.1⟩
  have hbound := (dimH_mono hsub).trans hdim
  rw [real_kernel_dimension _ hx.2.2] at hbound
  exact (hlocal _ hOS).not_ge hbound

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.RegularZero.Constructions.RegularZeroDimension
