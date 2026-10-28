import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.GermMaps

/-! # Germ Coordinate Equiv -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.GermCoordinateEquiv.AnalyticLocal

noncomputable section

/-! Holomorphic changes of coordinates induce ring equivalences on the
actual germ rings, with an explicit normalization on representatives. -/

open Set Filter
open scoped _root_.Topology

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

def holomorphicPullbackAt (f : F → E) (hf : Differentiable ℂ f) (y : F) (x : E) (hxy : f y = x) :
    ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x →+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm y :=
  hxy ▸ Holomorphic.GermMaps.AnalyticLocal.holomorphicComposition f hf y

theorem holomorphicPullbackAt_val (f : F → E) (hf : Differentiable ℂ f)
    (y : F) (x : E) (hxy : f y = x) (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x) :
    (holomorphicPullbackAt f hf y x hxy a).val =
      GermComposition.AnalyticLocal.germComposition f (by simpa only [hxy] using hf.continuous.tendsto y) a.val := by
  subst x
  rfl

theorem holomorphicPullbackAt_comp (f : F → E) (hf : Differentiable ℂ f)
    (g : G → F) (hg : Differentiable ℂ g) (x : E) (y : F) (z : G)
    (hfx : f y = x) (hgy : g z = y) :
    (holomorphicPullbackAt g hg z y hgy).comp (holomorphicPullbackAt f hf y x hfx) =
      holomorphicPullbackAt (f ∘ g) (hf.comp hg) z x (by simp only [Function.comp_apply, hgy, hfx]) := by
  subst y
  subst x
  exact Holomorphic.GermMaps.AnalyticLocal.holomorphicComposition_comp f hf g hg z

def holomorphicGermEquiv (e : E ≃ F) (he : Differentiable ℂ e) (hi : Differentiable ℂ e.symm)
    (x : E) : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x ≃+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm (e x) where
  __ := holomorphicPullbackAt e.symm hi (e x) x (e.symm_apply_apply x)
  invFun := holomorphicPullbackAt e he x (e x) rfl
  left_inv a := by
    obtain ⟨f, hfa, _⟩ := a.property
    apply Subtype.ext
    change (holomorphicPullbackAt e he x (e x) rfl
      (holomorphicPullbackAt e.symm hi (e x) x (e.symm_apply_apply x) a)).val = a.val
    rw [holomorphicPullbackAt_val, holomorphicPullbackAt_val, ← hfa]
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun p => by simp)
  right_inv a := by
    obtain ⟨f, hfa, _⟩ := a.property
    apply Subtype.ext
    change (holomorphicPullbackAt e.symm hi (e x) x (e.symm_apply_apply x)
      (holomorphicPullbackAt e he x (e x) rfl a)).val = a.val
    rw [holomorphicPullbackAt_val, holomorphicPullbackAt_val, ← hfa]
    apply Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall (fun p => by simp)

theorem holomorphicGermEquiv_val (e : E ≃ F) (he : Differentiable ℂ e)
    (hi : Differentiable ℂ e.symm) (x : E) (f : E → ℂ) {U : Set E}
    (hU : IsOpen U) (hx : x ∈ U) (hf : DifferentiableOn ℂ f U) :
    (holomorphicGermEquiv e he hi x (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction x f hU hx hf)).val =
      ((f ∘ e.symm) : Germ (𝓝 (e x)) ℂ) := by
  rw [show holomorphicGermEquiv e he hi x (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction x f hU hx hf) =
    holomorphicPullbackAt e.symm hi (e x) x (e.symm_apply_apply x) (ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.ofFunction x f hU hx hf) from rfl,
    holomorphicPullbackAt_val]
  rfl

def holomorphicGermEquivAt (e : E ≃ F) (he : Differentiable ℂ e) (hi : Differentiable ℂ e.symm)
    (x : E) (y : F) (hxy : e x = y) : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm x ≃+* ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm y :=
  hxy ▸ holomorphicGermEquiv e he hi x

theorem holomorphicGermEquivAt_symm_val (e : E ≃ F) (he : Differentiable ℂ e)
    (hi : Differentiable ℂ e.symm) (x : E) (y : F) (hxy : e x = y) (a : ComplexGroups.HolomorphicAlgebraicity.HolomorphicGerms.Constructions.Germs.HolomorphicGerm y) :
    ((holomorphicGermEquivAt e he hi x y hxy).symm a).val =
      GermComposition.AnalyticLocal.germComposition e (by simpa only [hxy] using he.continuous.tendsto x) a.val := by
  subst y
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.GermCoordinateEquiv.AnalyticLocal
