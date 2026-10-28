import OAI.Analysis.PDE.Dirichlet.CoordinateTransport
import OAI.Analysis.PDE.Dirichlet.Periodic.Calculus

/-! Fixed linear coordinate changes for the periodic global Schauder estimate. -/

open Set Module
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E F P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

omit [Fintype ι] in
theorem LatticePeriodic.comp_domain_equiv {W : Type*}
    {e : F ≃L[ℝ] P × V} {b : Basis ι ℝ P} {f : F → W}
    (hf : LatticePeriodic e b f) (L : E ≃L[ℝ] F) :
    LatticePeriodic (L.trans e) b (f ∘ L) := by
  intro x l
  simpa [Function.comp_def] using hf (L x) l

/-- Nonvanishing of the defining-function differential is invariant under
a genuine linear change of coordinates. -/
theorem regular_level_comp_equiv (L : E ≃L[ℝ] F) {r : F → ℝ}
    (hr : Differentiable ℝ r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0) :
    ∀ x, (r ∘ L) x = 0 → fderiv ℝ (r ∘ L) x ≠ 0 := by
  intro x hx hz
  apply hreg (L x) hx
  have hcomp : fderiv ℝ (r ∘ L) x = (fderiv ℝ r (L x)).comp L.toContinuousLinearMap := by
    rw [fderiv_comp x (hr (L x)) L.differentiableAt, L.fderiv]
  rw [hcomp] at hz
  ext v
  have hv := congrArg (fun A : E →L[ℝ] ℝ => A (L.symm v)) hz
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    L.apply_symm_apply, zero_apply] using hv

theorem sublevel_transverse_bound_comp_equiv
    (L : E ≃L[ℝ] F) (e : F ≃L[ℝ] P × V)
    {K : Set V} {r : F → ℝ}
    (hbound : ∀ x, r x ≤ 0 → (e x).2 ∈ K) :
    ∀ x, (r ∘ L) x ≤ 0 → ((L.trans e) x).2 ∈ K := by
  intro x hx
  exact hbound (L x) hx

omit [Fintype ι] in
/-- The flattened defining function has exactly the same periodic sublevel
geometry; in particular no new regular-boundary hypothesis is introduced. -/
theorem fourSlot_schauder_geometry {n : ℕ}
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {K : Set V} {r : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 3 r) (hrp : LatticePeriodic e b r)
    (hbound : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0) :
    ContDiff ℝ 3 (r ∘ (flattenFourSlots n).symm) ∧
    LatticePeriodic ((flattenFourSlots n).symm.toContinuousLinearEquiv.trans e) b
      (r ∘ (flattenFourSlots n).symm) ∧
    (∀ x, (r ∘ (flattenFourSlots n).symm) x ≤ 0 →
      (((flattenFourSlots n).symm.toContinuousLinearEquiv.trans e) x).2 ∈ K) ∧
    (∀ x, (r ∘ (flattenFourSlots n).symm) x = 0 →
      fderiv ℝ (r ∘ (flattenFourSlots n).symm) x ≠ 0) := by
  refine ⟨hr.comp (flattenFourSlots n).symm.contDiff,
    hrp.comp_domain_equiv (flattenFourSlots n).symm.toContinuousLinearEquiv,
    sublevel_transverse_bound_comp_equiv (flattenFourSlots n).symm.toContinuousLinearEquiv e hbound, ?_⟩
  exact regular_level_comp_equiv (flattenFourSlots n).symm.toContinuousLinearEquiv
    (hr.differentiable (by norm_num)) hreg

end OAI.Analysis.PDE.Dirichlet
