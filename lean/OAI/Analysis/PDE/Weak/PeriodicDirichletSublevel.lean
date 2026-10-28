import OAI.Analysis.PDE.Weak.PeriodicDirichletData
import OAI.Analysis.PDE.Dirichlet.Boundary.Normal

open Set Filter _root_.MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

theorem closure_strict_sublevel_of_regular {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : E → ℝ) (hr : ContDiff ℝ 1 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0) :
    closure {x | r x < 0} = {x | r x ≤ 0} := by
  apply Subset.antisymm
  · exact closure_minimal (fun x (hx : r x < 0) ↦ hx.le) (isClosed_le hr.continuous continuous_const)
  · intro x hx
    by_cases hz : r x = 0
    · obtain ⟨v,hv⟩ := OAI.Analysis.PDE.Dirichlet.linear_form_exists_negative (fderiv ℝ r x) (hreg x hz)
      have hline : HasDerivAt (fun t : ℝ ↦ x+t • v) v 0 := by
        simpa using (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x)
      have hr' : DifferentiableAt ℝ r (x+(0 : ℝ) • v) := by
        simpa using hr.differentiable (by norm_num) x
      have hslope : Tendsto (fun t : ℝ ↦ r (x+t • v)/t) (𝓝[>] 0)
          (𝓝 (fderiv ℝ r x v)) := by
        simpa [hz,div_eq_inv_mul] using
          (hr'.hasFDerivAt.comp_hasDerivAt 0 hline).tendsto_slope_zero_right
      have hpoint : Tendsto (fun t : ℝ ↦ x+t • v) (𝓝[>] 0) (𝓝 x) := by
        simpa using hline.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      apply mem_closure_of_tendsto hpoint
      filter_upwards [hslope.eventually (eventually_lt_nhds hv),self_mem_nhdsWithin] with t ht htp
      simpa using (div_lt_iff₀ (show 0 < t from htp)).mp ht
    · exact subset_closure (lt_of_le_of_ne hx hz)

variable {m : ℕ}

/-- Smooth periodic forcing produces an actual global smooth periodic
zero-Dirichlet solution. All L² representatives and boundary regularity
are constructed in the proof. -/
theorem exists_smooth_periodic_dirichlet_solution
    (J : Finset (Fin (m+1))) (a b : OAI.Analysis.PDE.Variational.CellCoordinates m) (hab : a ≤ b)
    (hL : ∀ i ∈ J, a i < b i)
    (r : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hr : ContDiff ℝ ∞ r)
    (hΩ : ∀ z x, r (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) < 0 → r x < 0)
    (k : Fin (m+1)) (hk : k ∉ J)
    (A : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m →L[ℝ] OAI.Analysis.PDE.Variational.CellVectors m) (hA : ContDiff ℝ ∞ A)
    (hAp : ∀ z x, A (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) = A x)
    (g : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hg : ContDiff ℝ ∞ g)
    (hgp : ∀ z x, g (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) = g x)
    {V : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hV : IsOpen V) {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ x ∈ V, ∀ z, lam*‖z‖^2 ≤ inner ℝ (A x z) z)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (htrans : {x | r x ≤ 0} ⊆ OAI.Analysis.PDE.Variational.transverseInterior J a b)
    (hcoeff : {x | r x ≤ 0} ⊆ V)
    (q : ℕ) (hq : 2 ≤ q) :
    ∃ v : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ, ContDiff ℝ q v ∧
      (∀ (z : J → ℤ) x, v (x+OAI.Analysis.PDE.Variational.coordinatePeriodShift J (b-a) z) = v x) ∧
      (∀ x, r x = 0 → v x = 0) ∧
      (∀ x, r x < 0 → -classicalDivergence (fun y ↦ A y (OAI.Analysis.PDE.Variational.cellGradient v y)) x = g x) := by
  have hcl := closure_strict_sublevel_of_regular r (hr.of_le (by simp)) hreg
  have hfg : ∀ᵐ y, r y < 0 → OAI.Analysis.PDE.Variational.periodicRepresentative J a b (OAI.Analysis.PDE.Variational.cellToL2 a b g hg.continuous) y = g y := by
    filter_upwards [periodicRepresentative_cellToL2_ae J a b hL g hg.continuous hgp] with y hy
    intro hyr
    apply hy
    intro i hi
    exact ⟨(htrans hyr.le i hi).1.le,(htrans hyr.le i hi).2.le⟩
  obtain ⟨u,v,_,hv,hvp,_,hvz,hve⟩ := exists_global_periodic_classical_dirichlet_solution
    J a b hab hL r hr hΩ k hk A hA hAp (OAI.Analysis.PDE.Variational.cellToL2 a b g hg.continuous) g hg hfg
    hV hlam hell hreg (by rwa [hcl]) (by rwa [hcl]) q hq
  refine ⟨v,hv,hvp,?_,hve⟩
  intro x hx
  apply hvz x
  rw [hcl]
  exact ⟨hx.le,by simp [hx]⟩

end OAI.Analysis.PDE.Weak
