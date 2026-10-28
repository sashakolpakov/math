import OAI.Analysis.Calculus.Coefficients.Bounds

open Set Filter _root_.MeasureTheory Module
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Calculus.Coefficients

open OAI.Analysis.PDE.Schauder OAI.Analysis.PDE.Dirichlet

variable {m : ℕ}

theorem smoothField_uniform_two_jet_bounds
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 3 f)
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : IsCompact K)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ B : ℝ, 0 < B ∧
      (∀ j x, x ∈ K → ‖smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f x‖ ≤ B) ∧
      (∀ j x, x ∈ K → ‖fderiv ℝ (smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f) x‖ ≤ B) ∧
      (∀ j x, x ∈ K → ‖fderiv ℝ (fderiv ℝ (smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f)) x‖ ≤ B) ∧
      (∀ j x, x ∈ K → ∀ y, y ∈ K →
        ‖fderiv ℝ (fderiv ℝ (smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f)) x-
          fderiv ℝ (fderiv ℝ (smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f)) y‖ ≤ B*dist x y^α) := by
  let : CompleteSpace (EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
  let : CompleteSpace (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := inferInstance
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hd1 : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hd2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) := hd1.fderiv_right (by norm_num)
  obtain ⟨B₀,hB₀,h₀⟩ := smoothField_uniform_bound_on_compact f hf.continuous hK
  obtain ⟨B₁,hB₁,h₁⟩ := smoothField_uniform_derivative_bound_on_compact f hf1 hK
  obtain ⟨B₂,hB₂,h₂⟩ := smoothField_uniform_bound_on_compact _ hd2.continuous hK
  obtain ⟨H,hH,hholder⟩ := smoothField_uniform_holder_on_compact _ hd2 hK hα hα1
  let B := B₀+B₁+B₂+H+1
  have h₀B : B₀ ≤ B := by dsimp [B]; linarith
  have h₁B : B₁ ≤ B := by dsimp [B]; linarith
  have h₂B : B₂ ≤ B := by dsimp [B]; linarith
  have hHB : H ≤ B := by dsimp [B]; linarith
  refine ⟨B,by dsimp [B]; positivity,
    fun j x hx ↦ (h₀ j x hx).trans h₀B,fun j x hx ↦ (h₁ j x hx).trans h₁B,?_,?_⟩
  · intro j x hx
    rw [second_fderiv_smoothField _ f hf2]
    exact (h₂ j x hx).trans h₂B
  · intro j x hx y hy
    rw [second_fderiv_smoothField _ f hf2]
    simpa only [dist_eq_norm] using (hholder j x hx y hy).trans
      (mul_le_mul_of_nonneg_right hHB (Real.rpow_nonneg (norm_nonneg _) _))

/-- Smooth the potential, not its cofactor. This supplies periodic smooth
potentials with compact-uniform C² convergence and common C²,α bounds, so
cofactors formed afterwards retain their exact divergence identities. -/
theorem exists_periodic_smooth_potential_approximation
    {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
    (e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (hf : ContDiff ℝ 3 f)
    (hfp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ u : ℕ → EuclideanSpace ℝ (Fin m) → ℝ,
      (∀ j, ContDiff ℝ ∞ (u j)) ∧ (∀ j, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (u j)) ∧
      ∀ K : Set (EuclideanSpace ℝ (Fin m)), IsCompact K →
        TendstoUniformlyOn u f atTop K ∧
        TendstoUniformlyOn (fun j ↦ fderiv ℝ (u j)) (fderiv ℝ f) atTop K ∧
        TendstoUniformlyOn (fun j ↦ fderiv ℝ (fderiv ℝ (u j))) (fderiv ℝ (fderiv ℝ f)) atTop K ∧
        ∃ B : ℝ, 0 < B ∧
          (∀ j x, x ∈ K → ‖u j x‖ ≤ B) ∧
          (∀ j x, x ∈ K → ‖fderiv ℝ (u j) x‖ ≤ B) ∧
          (∀ j x, x ∈ K → ‖fderiv ℝ (fderiv ℝ (u j)) x‖ ≤ B) ∧
          (∀ j x, x ∈ K → ∀ y, y ∈ K →
            ‖fderiv ℝ (fderiv ℝ (u j)) x-fderiv ℝ (fderiv ℝ (u j)) y‖ ≤ B*dist x y^α) := by
  refine ⟨fun j ↦ smoothField (OAI.Analysis.PDE.Schauder.standardMollifier m j) f,
    fun j ↦ contDiff_smoothField _ f hf.continuous,
    fun j ↦ smoothField_latticePeriodic e b _ f hfp,?_⟩
  intro K hK
  obtain ⟨h₀,h₁,h₂⟩ := smoothField_two_jet_tendstoUniformlyOn_compact f (hf.of_le (by norm_num)) hK
  exact ⟨h₀,h₁,h₂,smoothField_uniform_two_jet_bounds f hf hK hα hα1⟩

end OAI.Analysis.Calculus.Coefficients
