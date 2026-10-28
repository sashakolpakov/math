import OAI.Analysis.Calculus.Coefficients.Isometry

open Set Filter Module
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Calculus.Coefficients

open OAI.Analysis.PDE.Dirichlet

variable {E P V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

theorem exists_isometric_periodic_smooth_potential_approximation {m : ℕ}
    (L : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m))
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (f : E → ℝ) (hf : ContDiff ℝ 3 f) (hfp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ v : ℕ → E → ℝ,
      (∀ j, ContDiff ℝ ∞ (v j)) ∧ (∀ j, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (v j)) ∧
      ∀ K : Set E, IsCompact K →
        TendstoUniformlyOn v f atTop K ∧
        TendstoUniformlyOn (fun j ↦ fderiv ℝ (v j)) (fderiv ℝ f) atTop K ∧
        TendstoUniformlyOn (fun j ↦ fderiv ℝ (fderiv ℝ (v j))) (fderiv ℝ (fderiv ℝ f)) atTop K ∧
        ∃ B : ℝ, 0 < B ∧
          (∀ j x, x ∈ K → ‖v j x‖ ≤ B) ∧
          (∀ j x, x ∈ K → ‖fderiv ℝ (v j) x‖ ≤ B) ∧
          (∀ j x, x ∈ K → ‖fderiv ℝ (fderiv ℝ (v j)) x‖ ≤ B) ∧
          (∀ j x, x ∈ K → ∀ y, y ∈ K →
            ‖fderiv ℝ (fderiv ℝ (v j)) x-fderiv ℝ (fderiv ℝ (v j)) y‖ ≤ B*dist x y^α) := by
  let f' := f ∘ L.symm
  let e' := L.symm.toContinuousLinearEquiv.trans e
  have hf' : ContDiff ℝ 3 f' := hf.comp L.symm.contDiff
  have hp' : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e' b f' := by
    intro x l
    simpa [e',f'] using hfp (L.symm x) l
  have heq : f' ∘ L = f := by funext x; simp [f']
  obtain ⟨u,hu,hup,hudata⟩ := exists_periodic_smooth_potential_approximation e' b f' hf' hp' hα hα1
  refine ⟨fun j ↦ u j ∘ L,fun j ↦ (hu j).comp L.contDiff,?_,?_⟩
  · intro j x l
    have h := hup j (L x) l
    simpa [e'] using h
  · intro K hK
    obtain ⟨h₀,h₁,h₂,B,hB,hB₀,hB₁,hB₂,hBH⟩ := hudata (L '' K) (hK.image L.continuous)
    refine ⟨?_,?_,?_,B,hB,?_,?_,?_,?_⟩
    · apply Metric.tendstoUniformlyOn_iff.mpr
      intro ε hε
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp h₀ ε hε] with j hj
      intro x hx
      simpa [f'] using hj (L x) ⟨x,hx,rfl⟩
    · have h := first_jet_uniform_isometric_pullback L u f'
        (fun j ↦ (hu j).differentiable (by simp)) (hf'.differentiable (by norm_num)) h₁
      rwa [heq] at h
    · have h := second_jet_uniform_isometric_pullback L u f'
        (fun j ↦ (hu j).of_le (by simp)) (hf'.of_le (by norm_num)) h₂
      rwa [heq] at h
    · intro j x hx
      exact hB₀ j (L x) ⟨x,hx,rfl⟩
    · intro j x hx
      exact (first_fderiv_isometric_norm_le L (u j) ((hu j).differentiable (by simp)) x).trans
        (hB₁ j (L x) ⟨x,hx,rfl⟩)
    · intro j x hx
      exact (second_fderiv_isometric_norm_le L (u j) ((hu j).of_le (by simp)) x).trans
        (hB₂ j (L x) ⟨x,hx,rfl⟩)
    · intro j x hx y hy
      apply (second_fderiv_isometric_sub_norm_le L (u j) (u j)
        ((hu j).of_le (by simp)) ((hu j).of_le (by simp)) x y).trans
      simpa only [L.isometry.dist_eq] using hBH j (L x) ⟨x,hx,rfl⟩ (L y) ⟨y,hy,rfl⟩

theorem exists_fourSlot_periodic_smooth_potential_approximation {n : ℕ}
    (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (hf : ContDiff ℝ 3 f) (hfp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ v : ℕ → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ,
      (∀ j, ContDiff ℝ ∞ (v j)) ∧ (∀ j, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (v j)) ∧
      ∀ K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4), IsCompact K →
        TendstoUniformlyOn v f atTop K ∧
        TendstoUniformlyOn (fun j ↦ fderiv ℝ (v j)) (fderiv ℝ f) atTop K ∧
        TendstoUniformlyOn (fun j ↦ fderiv ℝ (fderiv ℝ (v j))) (fderiv ℝ (fderiv ℝ f)) atTop K ∧
        ∃ B : ℝ, 0 < B ∧
          (∀ j x, x ∈ K → ‖v j x‖ ≤ B) ∧
          (∀ j x, x ∈ K → ‖fderiv ℝ (v j) x‖ ≤ B) ∧
          (∀ j x, x ∈ K → ‖fderiv ℝ (fderiv ℝ (v j)) x‖ ≤ B) ∧
          (∀ j x, x ∈ K → ∀ y, y ∈ K →
            ‖fderiv ℝ (fderiv ℝ (v j)) x-fderiv ℝ (fderiv ℝ (v j)) y‖ ≤ B*dist x y^α) :=
  exists_isometric_periodic_smooth_potential_approximation (OAI.Analysis.PDE.Dirichlet.flattenFourSlots n) e b f hf hfp hα hα1

end OAI.Analysis.Calculus.Coefficients
