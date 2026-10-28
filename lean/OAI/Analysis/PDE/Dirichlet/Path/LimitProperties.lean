import OAI.Analysis.PDE.Dirichlet.Path.Solution
import OAI.Analysis.Normed.Function.Holder.C2HolderEquationLimit
import OAI.Analysis.Normed.Function.Holder.C2HolderLattice

open Set Module Filter
open scoped Topology BoundedContinuousFunction Matrix.Norms.Elementwise ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

theorem densityPath_banach_limit_properties {n : ℕ} {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : CoordinateSpace n 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {r B₀ F₀ F₁ : CoordinateSpace n 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 4 B₀) (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} {β : ℝ}
    (s : ℕ → SmoothPathSolution e lat r B₀ F₀ F₁)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hslim : Tendsto (fun k ↦ (s k).t) atTop (𝓝 t))
    (ψ : ℕ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK β) (g : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK β)
    (hlim : Tendsto ψ atTop (𝓝 g))
    (hv : ∀ k (x : {x | r x ≤ 0}), OAI.Analysis.Normed.Function.Holder.C2Holder.value (ψ k) x = B₀ x + (s k).u x)
    (hH : ∀ k (x : {x | r x ≤ 0}), OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (ψ k) x =
      fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + (s k).u y)) x)
    (hp : ∀ k, LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value (ψ k)))) :
    LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g)) ∧
      (∀ x : {x | r x ≤ 0}, r x = 0 → OAI.Analysis.Normed.Function.Holder.C2Holder.value g x = B₀ x) ∧
      (∀ x : {x | r x ≤ 0},
        OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK β OAI.Analysis.Calculus.Quaternion.fourSlots g) x) =
          densityPath F₀ F₁ t x ∧
        (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK β OAI.Analysis.Calculus.Quaternion.fourSlots g) x)).PosDef) ∧
      ∀ x : {x | r x ≤ 0},
        Tendsto (fun k ↦ B₀ x + (s k).u x) atTop (𝓝 (OAI.Analysis.Normed.Function.Holder.C2Holder.value g x)) := by
  have hpoint (x : {x | r x ≤ 0}) :
      Tendsto (fun k ↦ B₀ x + (s k).u x) atTop (𝓝 (OAI.Analysis.Normed.Function.Holder.C2Holder.value g x)) := by
    simpa only [hv] using OAI.Analysis.Normed.Function.Holder.C2Holder.value_tendsto hlim x
  have hperiod : LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value g)) := by
    apply (OAI.Analysis.Normed.Function.Holder.isClosed_latticeBCF e lat).mem_of_tendsto
      (OAI.Analysis.Normed.Function.Holder.C2Holder.valueCLM.continuous.tendsto g |>.comp hlim)
    exact Eventually.of_forall hp
  have hboundary (x : {x | r x ≤ 0}) (hx : r x = 0) : OAI.Analysis.Normed.Function.Holder.C2Holder.value g x = B₀ x := by
    apply tendsto_nhds_unique (hpoint x)
    simpa only [(s _).zero x hx, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ B₀ x) atTop (𝓝 (B₀ x)))
  have hfield (k) (x : {x | r x ≤ 0}) :
      OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩK β OAI.Analysis.Calculus.Quaternion.fourSlots (ψ k)) x =
      quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + (s k).u y) x :=
    quaternionHessianField_eq_of_secondDerivative_eq OAI.Analysis.Calculus.Quaternion.fourSlots (ψ k) _ x (hH k x)
  have heq (k) (x : {x | r x ≤ 0}) :
      OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + (s k).u y) x) =
        densityPath F₀ F₁ (s k).t x := by
    exact equality_on_regular_sublevel_of_interior (hr.of_le (by norm_num)) hreg
      (continuous_mooreHessian OAI.Analysis.Calculus.Quaternion.fourSlots ((hB₀.add (s k).smooth).of_le (by norm_num)))
      (contDiff_densityPath hF₀ hF₁ _).continuous
      (fun y hy ↦ (s k).equation y (neg_of_mem_interior_regular_sublevel hreg hy)) x x.property
  have hpositive (k) (x : {x | r x ≤ 0}) :
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + (s k).u y) x)).PosDef :=
    quaternionHessian_posDef_on_regular_sublevel (hr.of_le (by norm_num)) hreg
      ((hB₀.add (s k).smooth).of_le (by norm_num))
      (contDiff_densityPath hF₀ hF₁ _).continuous
      (fun y hy ↦ densityPath_pos (hpos₀ y hy) (hpos₁ y hy) (s k).parameter)
      (s k).positive (s k).equation x x.property
  refine ⟨hperiod, hboundary, ?_, hpoint⟩
  intro x
  have hc : Continuous (fun t : ℝ ↦ densityPath F₀ F₁ t x) := by
    unfold densityPath
    fun_prop
  apply mooreField_equation_posDef_limit hlim x ((hc.tendsto t).comp hslim)
    (densityPath_pos (hpos₀ x x.property) (hpos₁ x x.property) ht)
  · intro k
    rw [hfield]
    exact heq k x
  · intro k
    rw [hfield]
    exact hpositive k x

end OAI.Analysis.PDE.Dirichlet
