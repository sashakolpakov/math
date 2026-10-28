import OAI.NumberTheory.ArithmeticGroups.Lattices.NilpotentProductEquivariance
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContractingInverseFunctionTheorem

/-! # Nilpotent Product Homeomorphism -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.NilpotentProductHomeomorphism.Construction

noncomputable section

/-! Complementary subspaces preserved by a contracting algebra flow
give global exponential product coordinates on its nilpotent space. -/

open NormedSpace Filter
open scoped _root_.Topology

theorem exists_exponential_product_homeomorph
    {A ι : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
    (W : Submodule ℝ A) (hmul : ∀ x ∈ W, ∀ y ∈ W, x * y ∈ W)
    (hexp : ∀ x ∈ W, exp x - 1 ∈ W) (U V : Submodule ℝ W) (hUV : IsCompl U V)
    (R : ι → A ≃A[ℝ] A) (q : ι → W ≃L[ℝ] W)
    (hq : ∀ t (x : W), (q t x).val = R t x.val)
    (hU : ∀ t x, x ∈ U → q t x ∈ U) (hUi : ∀ t x, x ∈ U → (q t).symm x ∈ U)
    (hV : ∀ t x, x ∈ V → q t x ∈ V) (hVi : ∀ t x, x ∈ V → (q t).symm x ∈ V)
    (l : Filter ι) [NeBot l] (hcontract : ∀ x : W, Tendsto (fun t => q t x) l (𝓝 0)) :
    ∃ e : U × V ≃ₜ W, ∀ p, (e p).val = exp p.1.val.val * exp p.2.val.val - 1 := by
  let : NormedAddCommGroup W := inferInstance
  let : NormedSpace ℝ W := inferInstance
  let : NormedAddCommGroup U := inferInstance
  let : NormedSpace ℝ U := inferInstance
  let : NormedAddCommGroup V := inferInstance
  let : NormedSpace ℝ V := inferInstance
  let : NormedAddCommGroup (U × V) := inferInstance
  let : NormedSpace ℝ (U × V) := inferInstance
  let : CompleteSpace (U × V) := FiniteDimensional.complete ℝ (U × V)
  let f := NilpotentProductDerivative.Construction.exponentialProductCoordinates W hmul hexp U V
  let a : ι → U × V ≃ₜ U × V := fun t =>
    NilpotentProductEquivariance.Construction.invariantSubmoduleProductHomeomorph (q t) U V (hU t) (hUi t) (hV t) (hVi t)
  have ha : ∀ x : U × V, Tendsto (fun t => a t x) l (𝓝 0) := by
    intro x
    have hx : Tendsto (fun t => (a t x).1) l (𝓝 (0 : U)) := by
      apply Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr
      exact hcontract x.1.val
    have hy : Tendsto (fun t => (a t x).2) l (𝓝 (0 : V)) := by
      apply Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr
      exact hcontract x.2.val
    exact hx.prodMk_nhds hy
  have hb : ∀ y : W, Tendsto (fun t => (q t).toHomeomorph y) l (𝓝 (f 0)) := by
    intro y
    rw [show f 0 = 0 from NilpotentProductDerivative.Construction.exponentialProductCoordinates_zero W hmul hexp U V]
    exact hcontract y
  let de : (U × V) ≃L[ℝ] W := (U.prodEquivOfIsCompl V hUV).toContinuousLinearEquiv
  have hdf : HasStrictFDerivAt f de.toContinuousLinearMap 0 :=
    NilpotentProductDerivative.Construction.exponentialProductCoordinates_hasStrictFDerivAt W hmul hexp U V hUV
  obtain ⟨e, he⟩ := ContractingInverseFunctionTheorem.Construction.exists_homeomorph_of_contracting_strict_derivative (E := U × V) (F := W) f
    (NilpotentProductDerivative.Construction.exponentialProductCoordinates_continuous W hmul hexp U V)
    de 0 hdf
    a (fun t => (q t).toHomeomorph)
    (fun t p => NilpotentProductEquivariance.Construction.exponentialProductCoordinates_equivariant W hmul hexp U V
      (R t) (q t) (hq t) (hU t) (hUi t) (hV t) (hVi t) p) l ha hb
  refine ⟨e, fun p => ?_⟩
  exact congrArg Subtype.val (congrFun he p)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.NilpotentProductHomeomorphism.Construction
