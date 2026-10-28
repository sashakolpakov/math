import OAI.Analysis.PDE.Dirichlet.Periodic.SmoothJet
import OAI.Analysis.PDE.Dirichlet.Path.Solution
import OAI.Analysis.PDE.Dirichlet.Boundary.Continuity.Inverse

noncomputable section
open Set Filter Module
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4
local instance continuityBaseFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance continuityBaseFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance continuityBaseSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance continuityBaseSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem SmoothPathSolution.closed_equation
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P} {r B₀ F₀ F₁ : E → ℝ}
    (s : SmoothPathSolution e lat r B₀ F₀ F₁)
    (hr : ContDiff ℝ 1 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hB₀ : ContDiff ℝ 2 B₀) (hF₀ : Continuous F₀) (hF₁ : Continuous F₁) :
    ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet n
      (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x) = densityPath F₀ F₁ s.t x := by
  apply equality_on_regular_sublevel_of_interior hr hreg
    (continuous_mooreHessian OAI.Analysis.Calculus.Quaternion.fourSlots (hB₀.add (s.smooth.of_le (by norm_num))))
    ((continuous_const.mul hF₀).add (continuous_const.mul hF₁))
  intro x hx
  exact s.equation x (neg_of_mem_interior_regular_sublevel hreg hx)

theorem SmoothPathSolution.closed_positive
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P} {r B₀ F₀ F₁ : E → ℝ}
    (s : SmoothPathSolution e lat r B₀ F₀ F₁)
    (hr : ContDiff ℝ 1 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hB₀ : ContDiff ℝ 2 B₀) (hF₀ : Continuous F₀) (hF₁ : Continuous F₁)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x) :
    ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x)).PosDef :=
  quaternionHessian_posDef_on_regular_sublevel hr hreg
    (hB₀.add (s.smooth.of_le (by norm_num)))
    ((continuous_const.mul hF₀).add (continuous_const.mul hF₁))
    (fun x hx => densityPath_pos (hpos₀ x hx) (hpos₁ x hx) s.parameter) s.positive s.equation

def IsPathBanachBase
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {r B₀ F₀ F₁ : E → ℝ} {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (B : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) (s : SmoothPathSolution e lat r B₀ F₀ F₁)
    (u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat) : Prop :=
  ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value
    (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots (B+u.val)) x =
      quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y) x

theorem SmoothPathSolution.exists_banach_base
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hr : Continuous r) (hrp : LatticePeriodic e lat r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hB₀ : ContDiff ℝ 2 B₀) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (B : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hB₂ : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative B x = fderiv ℝ (fderiv ℝ B₀) x)
    (s : SmoothPathSolution e lat r B₀ F₀ F₁) :
    ∃ u : OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩD) (α := α) e lat,
      IsPathBanachBase e lat B s u := by
  obtain ⟨U,_,_,_,_,_,hU₂,hU⟩ := exists_periodic_dirichlet_C2Holder_jet e lat hK hr hrp hbounded
    s.u (s.smooth.of_le (by norm_num)) s.periodic s.zero hα hα1
  refine ⟨⟨U,hU⟩,?_⟩
  intro x
  apply quaternionHessianField_eq_of_secondDerivative_eq OAI.Analysis.Calculus.Quaternion.fourSlots (B+U) _ x
  change OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative B x+OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = _
  rw [hB₂,hU₂]
  exact (second_fderiv_add hB₀ (s.smooth.of_le (by norm_num)) x).symm

end OAI.Analysis.PDE.Dirichlet
