import OAI.Analysis.PDE.Dirichlet.Boundary.UniformDirichlet

noncomputable section
open Set Module Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Schauder

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V]
local notation "E" => CoordinateSpace (n+1) 4
local instance uniformClassicalFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance uniformClassicalFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance uniformClassicalSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance uniformClassicalSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def UniformPathClassicalEstimate
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK) (C : ℝ) : Prop :=
  ∀ (s : SmoothPathSolution e lat r B₀ F₀ F₁)
    (f : OAI.Analysis.Normed.Function.Holder.LatticeHolderSpace (K := {x | r x ≤ 0}) (α := d.exponent/2) e lat)
    (w : E → ℝ), ContDiff ℝ 2 w → LatticePeriodic e lat w →
    (∀ x, r x = 0 → w x = 0) →
    (∀ x (hx : r x < 0),
      mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y)) w x =
        OAI.Analysis.Normed.Function.Holder.HolderMap.value f.val ⟨x,hΩK hx⟩) →
    ∃ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK (d.exponent/2), ‖U‖ ≤ C*‖f‖ ∧
      U ∈ OAI.Analysis.Normed.Function.Holder.C2Holder.latticeDirichlet e lat ∧
      (∀ x : {x | r x ≤ 0}, w x = OAI.Analysis.Normed.Function.Holder.C2Holder.value U x) ∧
      (∀ x : {x | r x ≤ 0}, fderiv ℝ w x = OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x) ∧
      (∀ x : {x | r x ≤ 0}, fderiv ℝ (fderiv ℝ w) x = OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x)

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ V] [Nontrivial V] in
theorem InteriorThirdPathData.classical_estimate_of_uniform_solvability
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    [Nonempty {x | r x ≤ 0}]
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    {C : ℝ} (hsolve : UniformPathMooreSolvability e lat d C) :
    UniformPathClassicalEstimate e lat d C := by
  intro s f w hw hwp hwzero hwL
  have hψ : ContDiff ℝ 2 (fun y => B₀ y+s.u y) := (hB₀.add s.smooth).of_le (by norm_num)
  have hψpos := quaternionHessian_posDef_on_regular_sublevel
    (hr.of_le (by simp)) hreg hψ (contDiff_densityPath hF₀ hF₁ s.t).continuous
    (fun x hx => densityPath_pos (hpos₀ x hx) (hpos₁ x hx) s.parameter)
    s.positive s.equation
  have hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0} := by
    rw [OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular r (hr.of_le (by simp)) hreg]
  obtain ⟨c,hc,hclower⟩ := periodic_moore_defining_positive_lower (by omega) e lat hK
    (hr.of_le (by simp)) hrper hbounded hψ (hBper.add s.periodic) hrpos hψpos
  obtain ⟨U,hUnorm,hU,hUL⟩ := hsolve s f
  refine ⟨U,hUnorm,hU,?_⟩
  apply moore_classical_eq_banach_jets e lat hK (hr.of_le (by simp)) hrper hbounded
    hclosure (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y))
    (fun x hx => hψpos x hx.le) (fun x hx => hc.trans_le (hclower x hx.le))
    U hU w hw hwp hwzero
  intro x hx
  exact (hwL x hx).trans (hUL ⟨x,hΩK hx⟩).symm

theorem InteriorThirdPathData.uniform_classical_estimate
    (e : E ≃L[ℝ] P × V) (lat : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : E → ℝ} {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
    (d : OAI.Analysis.PDE.Schauder.InteriorThirdPathData e lat r B₀ F₀ F₁ hΩK)
    (hr : ContDiff ℝ ∞ r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    [Nonempty {x | r x ≤ 0}]
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hrpos : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)).PosDef)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x) :
    ∃ C > 0, UniformPathClassicalEstimate e lat d C := by
  obtain ⟨C,hC,hsolve⟩ := OAI.Analysis.PDE.Dirichlet.InteriorThirdPathData.uniform_moore_dirichlet_solvability
    e lat hK d hr hB₀ hF₀ hF₁ hrper hBper hp₀ hp₁ hbounded hreg hrpos hpos₀ hpos₁
  exact ⟨C,hC,OAI.Analysis.PDE.Dirichlet.InteriorThirdPathData.classical_estimate_of_uniform_solvability
    e lat hK d hr hB₀ hF₀ hF₁ hrper hBper hbounded hreg hrpos hpos₀ hpos₁ hsolve⟩

end OAI.Analysis.PDE.Dirichlet
