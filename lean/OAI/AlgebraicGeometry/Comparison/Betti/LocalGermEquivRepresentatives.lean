import OAI.AlgebraicGeometry.Comparison.Betti.Open.HolomorphicGermPullback

/-! # Local Germ Equiv Representatives -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.LocalGermEquivRepresentatives.Analytic

noncomputable section

section

/-! A local biholomorphism identifies the actual holomorphic germ rings,
with the literal forward and inverse function pullbacks. -/

open Set Filter
open scoped _root_.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def localHolomorphicGermEquiv (e : OpenPartialHomeomorph E F)
    (he : DifferentiableOn ℂ e e.source) (hi : DifferentiableOn ℂ e.symm e.target)
    (x : E) (hx : x ∈ e.source) : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x ≃+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (e x) where
  __ := Open.HolomorphicGermPullback.AnalyticLocal.openHolomorphicGermPullbackAt e.symm hi (e x) (e.map_source hx) x (e.left_inv hx)
  invFun := Open.HolomorphicGermPullback.AnalyticLocal.openHolomorphicGermPullbackAt e he x hx (e x) rfl
  left_inv a := by
    obtain ⟨f, hfa, _⟩ := a.property
    apply Subtype.ext
    change (Open.HolomorphicGermPullback.AnalyticLocal.openHolomorphicGermPullbackAt e he x hx (e x) rfl
      (Open.HolomorphicGermPullback.AnalyticLocal.openHolomorphicGermPullbackAt e.symm hi (e x) (e.map_source hx) x (e.left_inv hx) a)).val = a.val
    erw [Open.HolomorphicGermPullback.AnalyticLocal.openHolomorphicGermPullbackAt_val, Open.HolomorphicGermPullback.AnalyticLocal.openHolomorphicGermPullbackAt_val, ← hfa]
    apply Germ.coe_eq.mpr
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact congrArg f (e.left_inv hy)
  right_inv a := by
    obtain ⟨f, hfa, _⟩ := a.property
    apply Subtype.ext
    change (Open.HolomorphicGermPullback.AnalyticLocal.openHolomorphicGermPullbackAt e.symm hi (e x) (e.map_source hx) x (e.left_inv hx)
      (Open.HolomorphicGermPullback.AnalyticLocal.openHolomorphicGermPullbackAt e he x hx (e x) rfl a)).val = a.val
    erw [Open.HolomorphicGermPullback.AnalyticLocal.openHolomorphicGermPullbackAt_val, Open.HolomorphicGermPullback.AnalyticLocal.openHolomorphicGermPullbackAt_val, ← hfa]
    apply Germ.coe_eq.mpr
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    exact congrArg f (e.right_inv hy)

theorem localHolomorphicGermEquiv_symm_val (e : OpenPartialHomeomorph E F)
    (he : DifferentiableOn ℂ e e.source) (hi : DifferentiableOn ℂ e.symm e.target)
    (x : E) (hx : x ∈ e.source) (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (e x)) :
    ((localHolomorphicGermEquiv e he hi x hx).symm a).val =
      GermComposition.AnalyticLocal.germComposition e (e.continuousAt hx) a.val := rfl

def localHolomorphicGermEquivAt (e : OpenPartialHomeomorph E F)
    (he : DifferentiableOn ℂ e e.source) (hi : DifferentiableOn ℂ e.symm e.target)
    (x : E) (hx : x ∈ e.source) (y : F) (hxy : e x = y) : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x ≃+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm y :=
  hxy ▸ localHolomorphicGermEquiv e he hi x hx

theorem localHolomorphicGermEquivAt_symm_val (e : OpenPartialHomeomorph E F)
    (he : DifferentiableOn ℂ e e.source) (hi : DifferentiableOn ℂ e.symm e.target)
    (x : E) (hx : x ∈ e.source) (y : F) (hxy : e x = y) (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm y) :
    ((localHolomorphicGermEquivAt e he hi x hx y hxy).symm a).val =
      GermComposition.AnalyticLocal.germComposition e (by
        simpa only [hxy] using (show Tendsto e (𝓝 x) (𝓝 (e x)) from e.continuousAt hx)) a.val := by
  subst y
  rfl

end

/-! A local biholomorphic germ equivalence preserves the explicit pullback of every representative. -/

open Set Filter
open scoped _root_.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem localHolomorphicGermEquivAt_representative (e : OpenPartialHomeomorph E F)
    (he : DifferentiableOn ℂ e e.source) (hi : DifferentiableOn ℂ e.symm e.target)
    (x : E) (hx : x ∈ e.source) (y : F) (hxy : e x = y)
    (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x) (v : E → ℂ) (ha : a.val = (v : Germ (𝓝 x) ℂ)) :
    (localHolomorphicGermEquivAt e he hi x hx y hxy a).val =
      ((v ∘ e.symm) : Germ (𝓝 y) ℂ) := by
  subst y
  change (Open.HolomorphicGermPullback.AnalyticLocal.openHolomorphicGermPullbackAt e.symm hi (e x) (e.map_source hx) x (e.left_inv hx) a).val = _
  erw [Open.HolomorphicGermPullback.AnalyticLocal.openHolomorphicGermPullbackAt_val]
  rw [ha]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.LocalGermEquivRepresentatives.Analytic
