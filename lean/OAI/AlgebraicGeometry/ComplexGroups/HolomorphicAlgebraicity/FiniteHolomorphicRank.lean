import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicRegularity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Finite Holomorphic Rank -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FiniteHolomorphicRank.Constructions.FiniteRank

noncomputable section

/-!
# Derivative constraints imposed by finite holomorphic fibers
-/

open Set Filter _root_.Metric
open scoped _root_.Topology

theorem exists_nonzero_fderiv_of_finite_fiber
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {x : E} (hx : x ∈ U) (hfinite : {y | y ∈ U ∧ f y = f x}.Finite) :
    ∃ y ∈ U, fderiv ℂ f y ≠ 0 := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  by_contra hn
  have hzero : EqOn (fderiv ℂ f) 0 U := by
    intro y hy
    by_contra hny
    exact hn ⟨y, hy, hny⟩
  have hopen : IsOpen (U ∩ f ⁻¹' {f x}) :=
    hU.isOpen_inter_preimage_of_fderiv_eq_zero hf hzero {f x}
  have hnhds : {y | y ∈ U ∧ f y = f x} ∈ 𝓝 x := hopen.mem_nhds ⟨hx, rfl⟩
  exact infinite_of_mem_nhds x hnhds hfinite

theorem vertical_eq_zero_of_rank_le
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
    (L : E × F →L[ℂ] E × G) (hfst : ∀ p : E × F, (L p).1 = p.1)
    (hrank : Module.finrank ℂ L.toLinearMap.range ≤ Module.finrank ℂ E) (v : F) :
    L (0, v) = 0 := by
  let π : L.toLinearMap.range →ₗ[ℂ] E :=
    (LinearMap.fst ℂ E G).comp L.toLinearMap.range.subtype
  have hπ : Function.Surjective π := by
    intro x
    exact ⟨⟨L (x, 0), ⟨(x, 0), rfl⟩⟩, hfst (x, 0)⟩
  have hdim : Module.finrank ℂ L.toLinearMap.range = Module.finrank ℂ E :=
    le_antisymm hrank (LinearMap.finrank_le_finrank_of_surjective hπ)
  have hπinj : Function.Injective π :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hπ
  have hzero : (⟨L (0, v), ⟨(0, v), rfl⟩⟩ : L.toLinearMap.range) = 0 := by
    apply hπinj
    change (L (0, v)).1 = 0
    exact hfst (0, v)
  exact congrArg Subtype.val hzero

theorem not_finite_fiber_of_block_rank_bound
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [Nontrivial F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
    {f : E × F → E × G} {U : Set (E × F)} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hfst : ∀ p ∈ U, (f p).1 = p.1)
    (hrank : ∀ p ∈ U, Module.finrank ℂ (fderiv ℂ f p).toLinearMap.range ≤ Module.finrank ℂ E)
    {x : E × F} (hx : x ∈ U) :
    ¬{p | p ∈ U ∧ f p = f x}.Finite := by
  intro hfinite
  let V : Set F := (fun v => (x.1, v)) ⁻¹' U
  let g : F → E × G := fun v => f (x.1, v)
  have hV : IsOpen V := hU.preimage (continuous_const.prodMk continuous_id)
  have hxV : x.2 ∈ V := hx
  have hg : DifferentiableOn ℂ g V := hf.comp
    (differentiable_const x.1 |>.prodMk differentiable_id).differentiableOn (fun _ hp => hp)
  have hgfinite : {v | v ∈ V ∧ g v = g x.2}.Finite := by
    have hinj : Function.Injective (fun v : F => (x.1, v)) := fun _ _ h => congrArg Prod.snd h
    exact hfinite.preimage hinj.injOn
  obtain ⟨v, hv, hvd⟩ := exists_nonzero_fderiv_of_finite_fiber hV hg hxV hgfinite
  let p : E × F := (x.1, v)
  have hp : p ∈ U := hv
  have hfp := hf.differentiableAt (hU.mem_nhds hp)
  have hfstEq : (fun q => (f q).1) =ᶠ[𝓝 p] Prod.fst := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hfst q hq
  have hfstD : HasFDerivAt (fun q => (f q).1) (ContinuousLinearMap.fst ℂ E F) p :=
    hasFDerivAt_fst.congr_of_eventuallyEq hfstEq
  have hfstL (q : E × F) : ((fderiv ℂ f p) q).1 = q.1 :=
    congrArg (fun L : E × F →L[ℂ] E => L q) (hfp.hasFDerivAt.fst.unique hfstD)
  have hzero : (fderiv ℂ f p).comp (ContinuousLinearMap.inr ℂ E F) = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    exact vertical_eq_zero_of_rank_le (fderiv ℂ f p) hfstL (hrank p hp) w
  have hdg : HasFDerivAt g ((fderiv ℂ f p).comp (ContinuousLinearMap.inr ℂ E F)) v :=
    hfp.hasFDerivAt.comp v (hasFDerivAt_prodMk_right x.1 v)
  rw [hzero] at hdg
  exact hvd hdg.fderiv

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.FiniteHolomorphicRank.Constructions.FiniteRank
