import OAI.Analysis.PDE.Dirichlet.Path.GlobalHolder
import OAI.Analysis.Normed.Function.Holder.C2HolderUniformConstruct

open Set Module
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

/-- The manuscript's a-priori bound in the actual periodic C²,α Banach
space: every smooth path solution has its genuine value and two derivatives
represented, with one norm bound and exponent for all solutions. -/
theorem uniform_banach_bound_densityPath_lattice {n : ℕ} {P V ι : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : CoordinateSpace (n + 1) 4 ≃L[ℝ] P × V) (lat : Basis ι ℝ P)
    {K : Set V} (hK : IsCompact K)
    {r B₀ F₀ F₁ : CoordinateSpace (n + 1) 4 → ℝ} (hr : ContDiff ℝ 3 r)
    (hB₀ : ContDiff ℝ 4 B₀) (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (hrper : LatticePeriodic e lat r) (hBper : LatticePeriodic e lat B₀)
    (hp₀ : LatticePeriodic e lat F₀) (hp₁ : LatticePeriodic e lat F₁)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (hne : {x | r x ≤ 0}.Nonempty)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hpos₀ : ∀ x, r x ≤ 0 → 0 < F₀ x) (hpos₁ : ∀ x, r x ≤ 0 → 0 < F₁ x)
    (hbase : ∀ x, r x ≤ 0 → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hdet : ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet (n + 1) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) = 0)
    (hconvex : ∀ x, r x ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) Q))).PosSemidef)
    {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}} :
    ∃ α N : ℝ, 0 < α ∧ α < 1 ∧ 0 < N ∧
      ∃ Φ : SmoothPathSolution e lat r B₀ F₀ F₁ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α,
      ∀ s, ‖Φ s‖ ≤ N ∧
        (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.value (Φ s) x = B₀ x + s.u x) ∧
        (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative (Φ s) x =
          fderiv ℝ (fun z ↦ B₀ z + s.u z) x) ∧
        (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative (Φ s) x =
          fderiv ℝ (fderiv ℝ (fun z ↦ B₀ z + s.u z)) x) ∧
        LatticePeriodic e lat (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value (Φ s))) := by
  obtain ⟨α, H, hα, hα1, hH, hholder⟩ := uniform_global_holder_densityPath_lattice e lat hK
    hr hB₀ hF₀ hF₁ hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex
  obtain ⟨A, B, hA, hB, hgrad⟩ := uniform_value_gradient_densityPath_lattice e lat hK
    hr hB₀ hF₀ hF₁ hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex
  obtain ⟨M, hM, hhess⟩ := uniform_hessian_bound_densityPath_lattice e lat hK
    hr hB₀ hF₀ hF₁ hrper hBper hp₀ hp₁ hbounded hne hreg hr₀ hpos₀ hpos₁ hbase hdet hconvex
  let N := 1 + A + B + M + H
  have hN : 0 < N := by dsimp [N]; linarith
  have hAN : A ≤ N := by dsimp [N]; linarith
  have hBN : B ≤ N := by dsimp [N]; linarith
  have hMN : M ≤ N := by dsimp [N]; linarith
  have hHN : H ≤ N := by dsimp [N]; linarith
  obtain ⟨Φ, hΦ⟩ := OAI.Analysis.Normed.Function.Holder.exists_uniform_C2Holder (isOpen_lt hr.continuous continuous_const)
    hΩK hα.le hN.le (fun s : SmoothPathSolution e lat r B₀ F₀ F₁ ↦ fun z ↦ B₀ z + s.u z)
    (fun s ↦ (hB₀.add s.smooth).of_le (by norm_num))
    (fun s x hx ↦ ((hgrad s.t s.parameter s.u s.smooth s.periodic s.zero s.positive
      s.equation x hx).1).trans hAN)
    (fun s x hx ↦ ((hgrad s.t s.parameter s.u s.smooth s.periodic s.zero s.positive
      s.equation x hx).2).trans hBN)
    (fun s x hx ↦ (hhess s.t s.parameter s.u s.smooth s.periodic s.zero s.positive
      s.equation x hx).trans hMN)
    (fun s x hx y hy ↦ (hholder s x hx y hy).trans
      (mul_le_mul_of_nonneg_right hHN (Real.rpow_nonneg dist_nonneg _)))
  refine ⟨α, N, hα, hα1, hN, Φ, ?_⟩
  intro s
  obtain ⟨hn, hv, hD, hD₂⟩ := hΦ s
  refine ⟨hn, hv, hD, hD₂, ?_⟩
  exact OAI.Analysis.Normed.Function.Holder.latticePeriodic_of_value_eq (hrper.comp (fun t ↦ t ≤ 0)) (Φ s)
    (fun z ↦ B₀ z + s.u z) (hBper.add s.periodic) hv

end OAI.Analysis.PDE.Dirichlet
