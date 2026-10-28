import Mathlib.Geometry.Manifold.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # Local Maximum -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalMaximum.CM.Construction

noncomputable section

/-! Local maximum principles used for the intersection of the degree-one Hodge pieces. -/

open Set Filter Function
open scoped _root_.Topology _root_.Manifold

variable {M : Type*} [TopologicalSpace M]

/-- On a compact locally connected space, a continuous real function satisfying
the strong local maximum principle is locally constant. -/
theorem locallyConstant_of_localMaximumPrinciple
    [CompactSpace M] [LocallyConnectedSpace M] {f : M → ℝ}
    (hf : Continuous f)
    (hp : ∀ x, IsLocalMax f x → ∀ᶠ y in 𝓝 x, f y = f x) :
    IsLocallyConstant f := by
  apply IsLocallyConstant.of_constant_on_preconnected_clopens
  intro U hpc hcl a ha b hb
  obtain ⟨c, hcU, hc⟩ := hcl.isClosed.isCompact.exists_isMaxOn ⟨a, ha⟩ hf.continuousOn
  let V := {z ∈ U | f z = f c}
  have hVo : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    have hm : IsLocalMax f x :=
      mem_of_superset (hcl.isOpen.mem_nhds hx.1) fun z hz =>
        (hc hz).out.trans_eq hx.2.symm
    exact inter_mem (hcl.isOpen.mem_nhds hx.1)
      ((hp x hm).mono fun _ h => h.trans hx.2)
  let W := U ∩ {z | f z = f c}ᶜ
  have hWo : IsOpen W := hcl.isOpen.inter (isClosed_eq hf continuous_const).isOpen_compl
  have hdis : Disjoint V W := disjoint_compl_right.mono inf_le_right inf_le_right
  have hcover : U ⊆ V ∪ W := fun x hx => (eq_or_ne (f x) (f c)).imp (.intro hx) (.intro hx)
  have hVne : (U ∩ V).Nonempty := ⟨c, hcU, hcU, rfl⟩
  have hsub := hpc.subset_left_of_subset_union hVo hWo hdis hcover hVne
  exact (hsub hb).2.trans (hsub ha).2.symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]

/-- The real part of a local holomorphic function satisfies the strong local
maximum principle, by applying maximum modulus to its exponential. -/
theorem realPart_eventually_eq_of_localMax
    {g : M → ℂ} {x : M}
    (hg : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) g y)
    (hm : IsLocalMax (fun y => (g y).re) x) :
    ∀ᶠ y in 𝓝 x, (g y).re = (g x).re := by
  have hd : ∀ᶠ y in 𝓝 x,
      MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (Complex.exp ∘ g) y := by
    filter_upwards [hg] with y hy
    exact Complex.differentiable_exp.differentiableAt.mdifferentiableAt.comp y hy
  have hmax : IsLocalMax (norm ∘ (Complex.exp ∘ g)) x := by
    filter_upwards [hm] with y hy
    simpa only [Function.comp_apply, Complex.norm_exp] using Real.exp_le_exp.mpr hy
  have h := Complex.norm_eventually_eq_of_mdifferentiableAt_of_isLocalMax hd hmax
  filter_upwards [h] with y hy
  simpa only [Function.comp_apply, Complex.norm_exp, Real.exp_eq_exp] using hy

/-- A real function locally equal to the real part of a holomorphic function
is locally constant on a compact complex manifold. -/
theorem locallyRealPartHolomorphic_isLocallyConstant
    [CompactSpace M] {f : M → ℝ} (hf : Continuous f)
    (hl : ∀ x : M, ∃ g : M → ℂ,
      (∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) g y) ∧
      f =ᶠ[𝓝 x] fun y => (g y).re) : IsLocallyConstant f := by
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace E M
  apply locallyConstant_of_localMaximumPrinciple hf
  intro x hm
  obtain ⟨g, hg, heq⟩ := hl x
  have hcenter := heq.eq_of_nhds
  have hmax : IsLocalMax (fun y => (g y).re) x := by
    filter_upwards [hm, heq] with y hy he
    rwa [← he, ← hcenter]
  have h := realPart_eventually_eq_of_localMax hg hmax
  filter_upwards [h, heq] with y hy he
  exact he.trans (hy.trans hcenter.symm)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalMaximum.CM.Construction
