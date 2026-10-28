import OAI.Analysis.PDE.Schauder.Calculus.Interior.PathThird
import OAI.Analysis.PDE.Dirichlet.PointwiseHolderAbsorption
import OAI.Analysis.PDE.Dirichlet.Periodic.HigherJet

open Set Metric Module
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance pathGlobalThirdFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance pathGlobalThirdFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance pathGlobalThirdSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathGlobalThirdSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathGlobalThirdThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pathGlobalThirdThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The boundary-center estimate needed for the global nonlinear third
derivative bound. The radius is chosen before the small absorption parameter,
and all constants are independent of the actual solution along the path. -/
def BoundaryThirdPathEstimate
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P}
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK) : Prop :=
  ∀ x₀ : E, r x₀ = 0 → ∃ δ > 0, ∀ ε > 0, ∃ D > 0,
    ∀ s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁,
    ∀ T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) d.exponent,
    (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y))) x) →
    (∀ x ∈ closedBall x₀ δ, r x ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y))) x‖ ≤ ε*‖T‖+D) ∧
    (∀ x ∈ closedBall x₀ δ, r x ≤ 0 → ∀ y ∈ closedBall x₀ δ, r y ≤ 0 →
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+s.u z))) x-
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+s.u z))) y‖ ≤
          (ε*‖T‖+D)*dist x y^d.exponent)

/-- Boundary and interior center estimates have the same closed-domain form. -/
theorem InteriorThirdPathData.closed_local_third_estimate
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK) (hn : 3 ≤ n*4)
    (hr : Continuous r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hb : BoundaryThirdPathEstimate d) (x₀ : E) (hx₀ : r x₀ ≤ 0) :
    ∃ δ > 0, ∀ ε > 0, ∃ D > 0,
      ∀ s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁,
      ∀ T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) d.exponent,
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x =
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y))) x) →
      (∀ x ∈ closedBall x₀ δ, r x ≤ 0 →
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y))) x‖ ≤ ε*‖T‖+D) ∧
      (∀ x ∈ closedBall x₀ δ, r x ≤ 0 → ∀ y ∈ closedBall x₀ δ, r y ≤ 0 →
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+s.u z))) x-
          fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+s.u z))) y‖ ≤
            (ε*‖T‖+D)*dist x y^d.exponent) := by
  rcases lt_or_eq_of_le hx₀ with hxi | hxb
  · obtain ⟨δ,hδ,hlocal⟩ := d.local_third_estimate e lat hn hr hB₀ hF₀ hF₁ x₀ hxi
    refine ⟨δ,hδ,?_⟩
    intro ε hε
    obtain ⟨D,hD,hestimate⟩ := hlocal ε hε
    refine ⟨D,hD,?_⟩
    intro s T hT
    obtain ⟨hval,hholder⟩ := hestimate s T hT
    exact ⟨fun x hx _ => hval x hx, fun x hx _ y hy _ => by
      simpa only [dist_eq_norm] using hholder x hx y hy⟩
  · exact hb x₀ hxb

/-- The proved interior estimate and the boundary-center estimate give
one uniform global third-derivative Hölder bound. No a priori bound on the
third derivative, or on a fourth derivative, is used in the absorption. -/
theorem InteriorThirdPathData.uniform_third_norm_of_boundary
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK) (hn : 3 ≤ n*4)
    (hr : Continuous r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r) (hBp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat B₀)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hb : BoundaryThirdPathEstimate d)
    (T : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁ →
      OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) d.exponent)
    (hT : ∀ s (x : {x | r x ≤ 0}), OAI.Analysis.Normed.Function.Holder.HolderMap.value (T s) x =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y))) x) :
    ∃ M > 0, ∀ s, ‖T s‖ ≤ M := by
  let g (s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁) :=
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y)))
  have hgp (s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁) : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat (g s) :=
    (hBp.add s.periodic).fderiv.fderiv.fderiv
  obtain ⟨M,hM,hbound⟩ := OAI.Analysis.PDE.Dirichlet.lattice_holder_norm_absorption_of_pointwise
    e lat hK hr hrp hbounded d.exponent_pos g hgp T hT
    (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (by
      intro x₀
      have hclosed : r x₀ ≤ 0 := x₀.property.2
      obtain ⟨δ,hδ,hlocal⟩ := d.closed_local_third_estimate
        e lat hn hr hB₀ hF₀ hF₁ hb x₀ hclosed
      refine ⟨δ,hδ,?_⟩
      intro ε hε
      obtain ⟨D,hD,hestimate⟩ := hlocal ε hε
      refine ⟨D,hD,?_⟩
      intro s y hy
      have hyb : (y : E) ∈ closedBall (x₀ : E) δ := hy
      obtain ⟨hval,hholder⟩ := hestimate s (T s) (hT s)
      constructor
      · rw [mul_one]
        exact hval y hyb y.property.2
      · intro z hz
        have hzb : (z : E) ∈ closedBall (x₀ : E) δ := hz
        rw [mul_one]
        exact hholder y hyb y.property.2 z hzb z.property.2)
  exact ⟨M,hM,fun s => by simpa only [mul_one] using hbound s⟩

/-- Construct the actual third-derivative fields and absorb their norms,
without assuming any uniform bound for those fields. -/
theorem InteriorThirdPathData.uniform_third_holder_of_boundary
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK) (hn : 3 ≤ n*4)
    (hr : Continuous r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r) (hBp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat B₀)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hb : BoundaryThirdPathEstimate d) :
    ∃ M > 0, ∃ T : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁ →
      OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) d.exponent,
      ∀ s, ‖T s‖ ≤ M ∧ ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (T s) x =
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y))) x := by
  classical
  have hex (s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁) :=
    OAI.Analysis.PDE.Dirichlet.exists_periodic_third_derivative_field e lat hK hr hrp hbounded
      (fun y => B₀ y+s.u y) (hB₀.add s.smooth) (hBp.add s.periodic)
      d.exponent_pos.le d.exponent_lt_one.le
  choose T hT using hex
  obtain ⟨M,hM,hbound⟩ := d.uniform_third_norm_of_boundary
    e lat hK hn hr hB₀ hF₀ hF₁ hrp hBp hbounded hb T hT
  exact ⟨M,hM,T,fun s => ⟨hbound s,hT s⟩⟩

/-- Pointwise and Hölder forms of the global third derivative bound,
ready for the closed-domain compactness theorem. -/
theorem InteriorThirdPathData.uniform_third_bounds_of_boundary
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK) (hn : 3 ≤ n*4)
    (hr : Continuous r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat r) (hBp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e lat B₀)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hb : BoundaryThirdPathEstimate d) :
    ∃ M > 0, ∀ s : OAI.Analysis.PDE.Dirichlet.SmoothPathSolution e lat r B₀ F₀ F₁,
      (∀ x, r x ≤ 0 →
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => B₀ y+s.u y))) x‖ ≤ M) ∧
      (∀ x, r x ≤ 0 → ∀ y, r y ≤ 0 →
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+s.u z))) x-
          fderiv ℝ (fderiv ℝ (fderiv ℝ (fun z => B₀ z+s.u z))) y‖ ≤
            M*dist x y^d.exponent) := by
  obtain ⟨M,hM,T,hT⟩ := d.uniform_third_holder_of_boundary
    e lat hK hn hr hB₀ hF₀ hF₁ hrp hBp hbounded hb
  refine ⟨M,hM,?_⟩
  intro s
  constructor
  · intro x hx
    simpa only [(hT s).2] using (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le (T s) ⟨x,hx⟩).trans (hT s).1
  · intro x hx y hy
    have h := OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le (T s) ⟨x,hx⟩ ⟨y,hy⟩
    rw [(hT s).2, (hT s).2] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hT s).1 (Real.rpow_nonneg dist_nonneg _))

end OAI.Analysis.PDE.Schauder
