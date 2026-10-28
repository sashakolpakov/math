import OAI.Analysis.PDE.Dirichlet.Rough.InteriorDeformation
import OAI.Analysis.PDE.Dirichlet.Rough.InteriorRegularity
import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.ChartIsometry
import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.CurveGerms
import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.CurveMoore
import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.InverseJets

noncomputable section
open Set Filter Module Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.SmoothExtension

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

local instance geometricCurvesFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance geometricCurvesFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance geometricCurvesSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance geometricCurvesSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance geometricCurvesHolderGroup {Ω K : Set E} (h : Ω ⊆ K) (α : ℝ) :
    NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) h α) := inferInstance
local instance geometricCurvesHolderSpace {Ω K : Set E} (h : Ω ⊆ K) (α : ℝ) :
    NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) h α) := inferInstance

/-- A genuine smooth family of periodic domain diffeomorphisms near the
identity. This data records only geometry, not any regularity conclusion. -/
structure PeriodicDomainDeformation (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) (r : E → ℝ) where
  map : ℝ × E → E
  radius : ℝ
  radius_pos : 0 < radius
  smooth : ContDiff ℝ ∞ map
  at_zero : ∀ x, map (0,x) = x
  bijective : ∀ t : ℝ, |t| < radius → Function.Bijective (fun x ↦ map (t,x))
  inverse_smooth : ContDiffOn ℝ ∞
    (fun p : ℝ × E ↦ inverseFamily map p.1 p.2) {p | |p.1| < radius}
  equivariant : ∀ t (l : Submodule.span ℤ (Set.range b)) x,
    map (t,x+e.symm ((l:P),0)) = map (t,x)+e.symm ((l:P),0)
  open_domain : ∀ t : ℝ, |t| < radius → ∀ x, r (map (t,x)) < 0 ↔ r x < 0
  closed_domain : ∀ t : ℝ, |t| < radius → ∀ x, r (map (t,x)) ≤ 0 ↔ r x ≤ 0

/-- The precise output used from the parameterized implicit-function
argument. It asserts existence of actual Banach-space curves and their
pointwise geometric identity, not spatial differentiability of the solution. -/
def HasGeometricSolutionCurves
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) (r ψ B : E → ℝ)
    (hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}) (α : ℝ) : Prop :=
  ∀ D : PeriodicDomainDeformation e b r,
    ∃ U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ContDiffAt ℝ 2 U 0 ∧
      ∀ᶠ t in 𝓝 0, ∀ x : {x | r x ≤ 0},
        OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) x = ψ (D.map (t,x)) - B (D.map (t,x))

omit [Fintype ι] in
theorem latticeShiftHom_injective (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) :
    Function.Injective (OAI.Analysis.Calculus.SmoothExtension.latticeShiftHom e b) := by
  intro z w h
  apply Subtype.ext
  have he := congrArg (fun x : E ↦ (e x).1) h
  simpa only [OAI.Analysis.Calculus.SmoothExtension.latticeShiftHom,AddMonoidHom.coe_mk,ZeroHom.coe_mk,
    ContinuousLinearEquiv.apply_symm_apply] using he

omit [Fintype ι] in
theorem latticePeriodic_add_shift {F : Type*}
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {f : E → F}
    (hf : LatticePeriodic e b f) (x : E) (z : Submodule.span ℤ (Set.range b)) :
    f (x + OAI.Analysis.Calculus.SmoothExtension.latticeShiftHom e b z) = f x := by
  have hshift : x + OAI.Analysis.Calculus.SmoothExtension.latticeShiftHom e b z = e.symm ((e x).1 + (z : P),(e x).2) := by
    change x + e.symm ((z : P),0) = _
    simpa only [add_comm] using (lattice_translate_eq e x (z : P)).symm
  rw [hshift,hf x z]

section Geometry
variable [FiniteDimensional ℝ E] [Nontrivial E]

theorem exists_interior_periodicDomainDeformation
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (r : E → ℝ) (hr : Continuous r) (hrp : LatticePeriodic e b r)
    {a : E} (ha : r a < 0) (v : E) :
    ∃ D : PeriodicDomainDeformation e b r,
      D.map =ᶠ[𝓝 (0,a)] (fun p ↦ p.2 + p.1 • v) := by
  obtain ⟨Φ,d,hd,hΦ,hzero,hbij,hi,hper,hoff,hdom,hgerm⟩ :=
    exists_periodic_sublevel_interior_shift (OAI.Analysis.Calculus.SmoothExtension.latticeShiftHom e b)
      (latticeShiftHom_injective e b) (OAI.Analysis.Calculus.SmoothExtension.finite_latticeShiftHom_norm e b)
      r hr (latticePeriodic_add_shift e b hrp) ha v
  exact ⟨⟨Φ,d,hd,hΦ,hzero,hbij,hi,(fun t l x ↦ hper t x l),
    (fun t ht x ↦ (hdom t ht x).1),(fun t ht x ↦ (hdom t ht x).2)⟩,hgerm⟩

theorem exists_boundary_periodicDomainDeformation
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (j : X ≃ₗᵢ[ℝ] E) (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (r : E → ℝ) (hrp : LatticePeriodic e b r)
    {G : X → E} {P' : E → X} (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P')
    {a : E} (hG0 : G 0 = a)
    (hinv : (fun z ↦ P' (G z)) =ᶠ[𝓝 (0 : X)] id)
    (ℓ : X →L[ℝ] ℝ) (c : ℝ)
    (hlevel : ∀ z ∈ ball (0 : X) 1, r (G z) = c + ℓ z)
    (v : X) (hv : ℓ v = 0) :
    ∃ D : PeriodicDomainDeformation e b r,
      (fun p : ℝ × X ↦ D.map (p.1,G p.2)) =ᶠ[𝓝 (0,(0 : X))]
        (fun p ↦ G (p.2 + p.1 • v)) := by
  obtain ⟨Φ,d,hd,hΦ,hzero,hbij,hi,hper,hlevel',hgerm⟩ :=
    exists_periodic_chart_shift_isometry j (OAI.Analysis.Calculus.SmoothExtension.latticeShiftHom e b)
      (latticeShiftHom_injective e b) (OAI.Analysis.Calculus.SmoothExtension.finite_latticeShiftHom_norm e b)
      r (latticePeriodic_add_shift e b hrp) hG hP hG0 hinv ℓ c hlevel v hv
  refine ⟨⟨Φ,d,hd,hΦ,hzero,hbij,hi,(fun t l x ↦ hper t x l),?_,?_⟩,hgerm⟩
  · intro t ht x
    rw [hlevel' t ht x]
  · intro t ht x
    rw [hlevel' t ht x]

/-- Interior regularity is a proved consequence of the actual geometric
curve identity, with no a priori higher spatial derivatives. -/
theorem HasGeometricSolutionCurves.contDiffAt_four_interior
    {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P} {r ψ B : E → ℝ}
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hc : HasGeometricSolutionCurves e b r ψ B hΩD α)
    (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hψ : ContDiff ℝ 2 ψ) (hB : ContDiff ℝ 4 B) {a : E} (ha : r a < 0) :
    ContDiffAt ℝ 4 ψ a := by
  apply contDiffAt_four_of_interior_geometric_curves (hΩK := hΩD) (α := α)
    (isOpen_lt hr continuous_const) ha hψ hB
  intro v
  obtain ⟨D,hD⟩ := exists_interior_periodicDomainDeformation e b r hr hrp ha v
  obtain ⟨U,hU,he⟩ := hc D
  obtain ⟨O,hO,haO,hgerm⟩ := translation_curve_germs
    (G := id) (S := {x | r x < 0}) (fun x hx ↦ hΩD hx) he hD
  exact ⟨O,hO,haO,U,hU,hgerm⟩

end Geometry
end OAI.Analysis.PDE.Dirichlet
