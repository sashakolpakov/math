import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion

/-! # Quadratic Sections -/

namespace OAI.RepresentationTheory.Theta.Geometric.QuadraticSections.RiemannProjectivityConstruction

noncomputable section

/-! Two opposite translates give basepoint-free sections of degree two.
Together with the cubic sections, these supply consecutive powers. -/

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (Λ : AddSubgroup V) [DiscreteTopology Λ]

def thetaPair (a z : V) : ℂ := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.theta H Λ (z - a) * Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.theta H Λ (z + a)

theorem thetaPair_differentiable
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (a : V) :
    Differentiable ℂ (thetaPair H Λ a) := by
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  exact ((Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.theta_differentiable H Λ hpos).comp (differentiable_id.sub_const a)).mul
    ((Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.theta_differentiable H Λ hpos).comp (differentiable_id.add_const a))

omit [FiniteDimensional ℂ V] [DiscreteTopology Λ] in
theorem thetaPair_translation
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (a : V) (l : Λ) (z : V) :
    thetaPair H Λ a (z + l) = Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy H l z ^ 2 * thetaPair H Λ a z := by
  have hfactor : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy H l (z - a) * Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy H l (z + a) =
      Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy H l z ^ 2 := by
    simp only [Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy, ← Complex.exp_add, ← Complex.exp_nat_mul]
    congr 1
    simp only [map_sub, map_add]
    ring
  unfold thetaPair
  rw [show z + (l : V) - a = (z - a) + l by abel,
    show z + (l : V) + a = (z + a) + l by abel,
    Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.theta_translation H hsym Λ hint, Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.theta_translation H hsym Λ hint]
  calc
    _ = (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy H l (z - a) * Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.doubledAutomorphy H l (z + a)) *
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.theta H Λ (z - a) * Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.theta H Λ (z + a)) := by ring
    _ = _ := by rw [hfactor]

theorem exists_thetaPair_ne_zero
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re) (z : V) :
    ∃ a : V, thetaPair H Λ a z ≠ 0 := by
  let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  by_contra! hzero
  let f : ℂ → ℂ := fun t => Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.theta H Λ (z - t • z)
  let g : ℂ → ℂ := fun t => Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.theta H Λ (z + t • z)
  have hf : Differentiable ℂ f := (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.theta_differentiable H Λ hpos).comp
    ((differentiable_const z).sub (differentiable_id.smul_const z))
  have hg : Differentiable ℂ g := (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.theta_differentiable H Λ hpos).comp
    ((differentiable_const z).add (differentiable_id.smul_const z))
  have hf' : AnalyticOnNhd ℂ f Set.univ := fun t _ => hf.analyticAt t
  have hg' : AnalyticOnNhd ℂ g Set.univ := fun t _ => hg.analyticAt t
  have hfg : ∀ t ∈ (Set.univ : Set ℂ), f t * g t = 0 := fun t _ => hzero (t • z)
  rcases hf'.eq_zero_or_eq_zero_of_mul_eq_zero hg' hfg isPreconnected_univ with h | h
  · have hz := h 1 (Set.mem_univ _)
    have hn := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.theta_at_zero_ne_zero H Λ hsym hpos
    simp [f, hn] at hz
  · have hz := h (-1) (Set.mem_univ _)
    have hn := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.theta_at_zero_ne_zero H Λ hsym hpos
    simp [g, hn] at hz

def pairSection
    (hsym : ∀ u v : V, H v u = star (H u v))
    (hpos : ∀ u : V, u ≠ 0 → 0 < (H u u).re)
    (hint : ∀ u ∈ Λ, ∀ v ∈ Λ, ∃ m : ℤ, (H u v).im = (m : ℝ))
    (a : V) : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.ThetaSection H Λ 2 where
  toFun := thetaPair H Λ a
  regular := by
    let : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
    exact ((Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.theta_contDiff_one H Λ hpos).comp (contDiff_id.sub contDiff_const)).mul
      ((Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.theta_contDiff_one H Λ hpos).comp (contDiff_id.add contDiff_const))
  translates := thetaPair_translation H Λ hsym hint a

end

end OAI.RepresentationTheory.Theta.Geometric.QuadraticSections.RiemannProjectivityConstruction
