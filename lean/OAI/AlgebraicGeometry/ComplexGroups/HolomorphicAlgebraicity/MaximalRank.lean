import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearRankCoordinates
import Mathlib.Data.Nat.Find

/-! # Maximal Rank -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.MaximalRank.Constructions.FiniteRank

noncomputable section

/-!
# A locally maximal derivative rank at a finite fiber is full
-/

open Set Filter
open scoped _root_.Topology

theorem injective_fderiv_of_locally_maximal_rank
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    {x : E} (hx : x ∈ U) (hfinite : {y | y ∈ U ∧ f y = f x}.Finite)
    (hmax : ∀ y ∈ U, Module.finrank ℂ (fderiv ℂ f y).toLinearMap.range ≤
      Module.finrank ℂ (fderiv ℂ f x).toLinearMap.range) :
    Function.Injective (fderiv ℂ f x) := by
  classical
  let L := fderiv ℂ f x
  by_contra hnot
  have hker : L.toLinearMap.ker ≠ ⊥ := by
    intro h
    exact hnot (LinearMap.ker_eq_bot.mp h)
  let : Nontrivial L.toLinearMap.ker := Submodule.nontrivial_iff_ne_bot.mpr hker
  obtain ⟨π, κ, e, _, he⟩ := LinearRankCoordinates.Constructions.FiniteRank.exists_rank_coordinates L
  let φ : E → L.toLinearMap.range × L.toLinearMap.ker := fun y => (π (f y), κ y)
  have hφ : DifferentiableOn ℂ φ U :=
    (π.differentiable.comp_differentiableOn hf).prodMk κ.differentiable.differentiableOn
  have hfx := hf.differentiableAt (hU.mem_nhds hx)
  have hdφ : HasFDerivAt φ ((π.comp L).prod κ) x :=
    (π.hasFDerivAt.comp x hfx.hasFDerivAt).prodMk κ.hasFDerivAt
  have hφe : fderiv ℂ φ x = e.toContinuousLinearMap := hdφ.fderiv.trans he.symm
  obtain ⟨q, hxq, hqφ, _, hqinv⟩ := HolomorphicRegularity.Constructions.Regularity.exists_holomorphic_localInverse hU hφ hx e hφe
  let V := q.target ∩ q.symm ⁻¹' U
  have hV : IsOpen V := q.continuousOn_symm.isOpen_inter_preimage q.open_target hU
  have hb : q x ∈ V := ⟨q.map_source hxq, by simpa only [mem_preimage, q.left_inv hxq] using hx⟩
  let g : L.toLinearMap.range × L.toLinearMap.ker → F := fun p => f (q.symm p)
  let T : L.toLinearMap.range × L.toLinearMap.ker → L.toLinearMap.range × F :=
    fun p => (p.1, g p)
  let C : F →L[ℂ] L.toLinearMap.range × F := π.prod (ContinuousLinearMap.id ℂ F)
  have hg : DifferentiableOn ℂ g V := hf.comp (hqinv.mono inter_subset_left) (fun _ hp => hp.2)
  have hT : DifferentiableOn ℂ T V := differentiable_fst.differentiableOn.prodMk hg
  have hTC (p : L.toLinearMap.range × L.toLinearMap.ker) (hp : p ∈ V) : T p = C (g p) := by
    have h := congrArg Prod.fst (q.right_inv hp.1)
    have hπg : π (g p) = p.1 := by
      change (q (q.symm p)).1 = p.1 at h
      rw [hqφ] at h
      exact h
    exact Prod.ext hπg.symm rfl
  have hTrank (p : L.toLinearMap.range × L.toLinearMap.ker) (hp : p ∈ V) :
      Module.finrank ℂ (fderiv ℂ T p).toLinearMap.range ≤ Module.finrank ℂ L.toLinearMap.range := by
    have hdf := (hf.differentiableAt (hU.mem_nhds hp.2)).hasFDerivAt
    have hdq := (hqinv.differentiableAt (q.open_target.mem_nhds hp.1)).hasFDerivAt
    have hdg : HasFDerivAt g ((fderiv ℂ f (q.symm p)).comp (fderiv ℂ q.symm p)) p :=
      hdf.comp p hdq
    have hTeq : T =ᶠ[𝓝 p] (fun z => C (g z)) := by
      filter_upwards [hV.mem_nhds hp] with z hz
      exact hTC z hz
    have hdT := (C.hasFDerivAt.comp p hdg).congr_of_eventuallyEq hTeq
    rw [hdT.fderiv]
    exact (LinearRankCoordinates.Constructions.FiniteRank.finrank_range_comp_le_middle C.toLinearMap (fderiv ℂ f (q.symm p)).toLinearMap
      (fderiv ℂ q.symm p).toLinearMap).trans (hmax (q.symm p) hp.2)
  have hTfinite : {p | p ∈ V ∧ T p = T (q x)}.Finite := by
    apply Set.Finite.of_injOn (f := q.symm) _ _ hfinite
    · intro p hp
      refine ⟨hp.1.2, ?_⟩
      have h := congrArg Prod.snd hp.2
      change f (q.symm p) = f (q.symm (q x)) at h
      simpa only [q.left_inv hxq] using h
    · intro p hp r hr heq
      exact q.symm.injOn hp.1.1 hr.1.1 heq
  exact FiniteHolomorphicRank.Constructions.FiniteRank.not_finite_fiber_of_block_rank_bound hV hT (fun _ _ => rfl) hTrank hb hTfinite

theorem exists_injective_fderiv_of_finite_fibers
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hne : U.Nonempty)
    (hf : DifferentiableOn ℂ f U) (hfinite : ∀ v : F, {y | y ∈ U ∧ f y = v}.Finite) :
    ∃ x ∈ U, Function.Injective (fderiv ℂ f x) := by
  classical
  let r : E → ℕ := fun y => Module.finrank ℂ (fderiv ℂ f y).toLinearMap.range
  let m := Module.finrank ℂ E
  let D := Nat.findGreatest (fun k => ∃ y ∈ U, r y = k) m
  have hr (y : E) : r y ≤ m := LinearMap.finrank_range_le (fderiv ℂ f y).toLinearMap
  obtain ⟨x₀, hx₀⟩ := hne
  have hD : ∃ y ∈ U, r y = D := Nat.findGreatest_spec
    (P := fun k => ∃ y ∈ U, r y = k) (hr x₀) ⟨x₀, hx₀, rfl⟩
  obtain ⟨x, hx, hxD⟩ := hD
  refine ⟨x, hx, injective_fderiv_of_locally_maximal_rank hU hf hx (hfinite (f x)) ?_⟩
  intro y hy
  change r y ≤ r x
  rw [hxD]
  exact Nat.le_findGreatest (P := fun k => ∃ z ∈ U, r z = k) (hr y) ⟨y, hy, rfl⟩

theorem dense_injective_fderiv_of_finite_fibers
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
    {f : E → F} {U : Set E} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hfinite : ∀ v : F, {y | y ∈ U ∧ f y = v}.Finite) :
    U ⊆ closure {y | y ∈ U ∧ Function.Injective (fderiv ℂ f y)} := by
  intro x hx
  apply Metric.mem_closure_iff.mpr
  intro r hr
  have hV : IsOpen (U ∩ Metric.ball x r) := hU.inter Metric.isOpen_ball
  have hne : (U ∩ Metric.ball x r).Nonempty := ⟨x, hx, Metric.mem_ball_self hr⟩
  obtain ⟨y, hy, hyD⟩ := exists_injective_fderiv_of_finite_fibers hV hne
    (hf.mono inter_subset_left)
    (fun v => (hfinite v).subset (fun _ hy => ⟨hy.1.1, hy.2⟩))
  exact ⟨y, ⟨hy.1, hyD⟩, by simpa only [dist_comm] using Metric.mem_ball.mp hy.2⟩

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.MaximalRank.Constructions.FiniteRank
