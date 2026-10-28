import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Method
import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Step
import OAI.Analysis.PDE.Dirichlet.Rough.Moore.C4Regularity

noncomputable section
open Set Filter Module
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
local notation "E" => CoordinateSpace n 4
local instance continuityOpenFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance continuityOpenFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance continuityOpenSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance continuityOpenSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The actual smooth solution set is relatively open in the density path.
Rough implicit solutions are upgraded to C⁴ before being included in this set. -/
theorem SmoothPathSolution.solvable_near
    (hn : 1 ≤ n) (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ}
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ ∞ B₀)
    (hF₀ : ContDiff ℝ ∞ F₀) (hF₁ : ContDiff ℝ ∞ F₁)
    (hrp : LatticePeriodic e lat r) (hB₀p : LatticePeriodic e lat B₀)
    (hF₀p : LatticePeriodic e lat F₀) (hF₁p : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K) [Nonempty {x | r x ≤ 0}]
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (s : SmoothPathSolution e lat r B₀ F₀ F₁) :
    ∀ᶠ t in 𝓝 s.t, t ∈ Icc (0 : ℝ) 1 → SmoothPathSolvable e lat r B₀ F₀ F₁ t := by
  let : NeZero n := ⟨by omega⟩
  let hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0} := fun x hx => (show r x < 0 from hx).le
  let hΩ : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
  have hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0} := by
    rw [OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular r (hr.of_le (by simp)) hreg]
  obtain ⟨B,_,_,_,hBv,hB₁,hB₂,hBp⟩ := exists_periodic_C2Holder_jet
    (hΩD := hΩD) (α := (1/2:ℝ)) e lat hK hr.continuous hrp hbounded B₀
    (hB₀.of_le (by simp)) hB₀p (by norm_num) (by norm_num)
  have hrough := s.rough_continuation hn e lat hK hr (hB₀.of_le (by simp))
    (hF₀.of_le (by simp)) (hF₁.of_le (by simp)) hrp hB₀p hF₀p hF₁p hbounded
    hreg hrpos hpos₀ hpos₁ hΩ hclosure (by norm_num : (0:ℝ)<1/2) (by norm_num)
    B hBp hB₂
  filter_upwards [hrough] with t ht
  intro hparam
  obtain ⟨u,hupos,hueq,huinv⟩ := ht
  have hft : ContDiff ℝ ∞ (densityPath F₀ F₁ t) :=
    (contDiff_const.mul hF₀).add (contDiff_const.mul hF₁)
  obtain ⟨ψ,hψ,hψp,hψbd,_,_,_,hψpos,hψeq⟩ :=
    exists_periodic_C4_representative_of_invertible hn hK hr hrp hbounded hreg
      (fun x hx => hrpos x hx.le) (by norm_num : (0:ℝ)<1/2) (by norm_num)
      B₀ (densityPath F₀ F₁ t) hB₀ hft hB₀p (densityPath_periodic e lat hF₀p hF₁p t)
      B hBp hBv hB₁ hB₂ u hupos hueq hΩ hclosure huinv
  exact OAI.Analysis.PDE.Dirichlet.SmoothPathSolvable.of_classical_potential e lat hparam (hB₀.of_le (by simp)) hB₀p
    ψ hψ hψp hψbd hψpos hψeq

end OAI.Analysis.PDE.Dirichlet
