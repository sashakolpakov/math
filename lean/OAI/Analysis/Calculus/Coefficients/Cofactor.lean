import OAI.Analysis.Calculus.Coefficients.FourSlots
import OAI.Analysis.Calculus.Coefficients.Composition
import OAI.Analysis.PDE.Dirichlet.Moore.Matrix

open Set Filter Module Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.Calculus.Coefficients

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {n : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

local instance coefficientFirstNormedGroup : NormedAddCommGroup (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance coefficientFirstNormedSpace : NormedSpace ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance coefficientSecondNormedGroup : NormedAddCommGroup
    (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance coefficientSecondNormedSpace : NormedSpace ℝ
    (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance

/-- Apply a smooth finite-dimensional function to the genuine quaternionic
Hessians of a uniformly bounded family of second jets. -/
theorem quaternionHessian_composition_approximation
    (Φ : Matrix (Fin n) (Fin n) (Quaternion ℝ) → G) (hΦ : ContDiff ℝ 1 Φ)
    (u : ℕ → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ)
    (hf : ContDiff ℝ 2 f) {K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} (hK : IsCompact K)
    (hc : TendstoUniformlyOn (fun j ↦ fderiv ℝ (fderiv ℝ (u j)))
      (fderiv ℝ (fderiv ℝ f)) atTop K)
    {B α : ℝ} (hB : 0 ≤ B)
    (hu : ∀ j x, x ∈ K → ‖fderiv ℝ (fderiv ℝ (u j)) x‖ ≤ B)
    (hh : ∀ j x, x ∈ K → ∀ y, y ∈ K →
      ‖fderiv ℝ (fderiv ℝ (u j)) x-fderiv ℝ (fderiv ℝ (u j)) y‖ ≤ B*dist x y^α) :
    TendstoUniformlyOn (fun j x ↦ Φ (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x))
      (fun x ↦ Φ (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)) atTop K ∧
    ∃ C : ℝ, 0 < C ∧
      (∀ j x, x ∈ K → ‖Φ (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)‖ ≤ C) ∧
      (∀ j x, x ∈ K → ∀ y, y ∈ K →
        ‖Φ (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)-Φ (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) y)‖
          ≤ C*dist x y^α) := by
  let J := OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM (m := n) OAI.Analysis.Calculus.Quaternion.fourSlots
  have hfD : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (by norm_num : (1 : ℕ∞ω)+1 ≤ 2)).continuous_fderiv one_ne_zero
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hfD.continuousOn
  have huR j x (hx : x ∈ K) : ‖fderiv ℝ (fderiv ℝ (u j)) x‖ ≤ max B M :=
    (hu j x hx).trans (le_max_left _ _)
  have hfR x (hx : x ∈ K) : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ max B M :=
    (hM x hx).trans (le_max_right _ _)
  exact smooth_composition_uniform_holder (Φ ∘ J) (hΦ.comp J.contDiff)
    (fun j ↦ fderiv ℝ (fderiv ℝ (u j))) (fderiv ℝ (fderiv ℝ f)) hc
    (hB.trans (le_max_left _ _)) hB huR hfR hh

theorem contDiff_quaternionHessian_smooth
    {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hD₂ : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) := hD.fderiv_right (by simp)
  exact (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM (m := n) OAI.Analysis.Calculus.Quaternion.fourSlots).contDiff.comp hD₂

variable {P V ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Smooth the potential itself. Thus the approximating coefficient fields
are actual Moore cofactors and their column divergence vanishes exactly. -/
theorem exists_periodic_smooth_cofactor_approximation
    (e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (hf : ContDiff ℝ 3 f) (hfp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b f)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ u : ℕ → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ,
      (∀ j, ContDiff ℝ ∞ (u j)) ∧ (∀ j, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (u j)) ∧
      (∀ j, ContDiff ℝ ∞ (fun x ↦ OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x))) ∧
      (∀ j, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x ↦ OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x))) ∧
      (∀ j x q, (∑ p, fderiv ℝ (fun y ↦ OAI.Analysis.PDE.Dirichlet.mooreRealMatrix
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) y) p q) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) = 0) ∧
      ∀ K : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4), IsCompact K →
        TendstoUniformlyOn (fun j x ↦ OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x))
          (fun x ↦ OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)) atTop K ∧
        TendstoUniformlyOn (fun j x ↦ OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x))
          (fun x ↦ OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots f x)) atTop K ∧
        ∃ C : ℝ, 0 < C ∧
          (∀ j x, x ∈ K → ‖OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)‖ ≤ C) ∧
          (∀ j x, x ∈ K → ‖OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)‖ ≤ C) ∧
          (∀ j x, x ∈ K → ∀ y, y ∈ K →
            ‖OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)-
              OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) y)‖ ≤ C*dist x y^α) ∧
          (∀ j x, x ∈ K → ∀ y, y ∈ K →
            ‖OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) x)-
              OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u j) y)‖ ≤ C*dist x y^α) := by
  obtain ⟨u,hu,hup,hdata⟩ := exists_fourSlot_periodic_smooth_potential_approximation e b f hf hfp hα hα1
  refine ⟨u,hu,hup,?_,?_,?_,?_⟩
  · intro j
    exact (OAI.Analysis.PDE.Dirichlet.contDiff_mooreRealMatrix n ∞).comp (contDiff_quaternionHessian_smooth (hu j))
  · intro j
    exact ((hup j).quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots).comp OAI.Analysis.PDE.Dirichlet.mooreRealMatrix
  · intro j x q
    exact OAI.Analysis.PDE.Dirichlet.mooreRealMatrix_divergence ((hu j).of_le (by simp)) x q
  · intro K hK
    obtain ⟨_,_,hc,B,hB,_,_,hBD,hBH⟩ := hdata K hK
    obtain ⟨hcM,M,hM,hMB,hMH⟩ := quaternionHessian_composition_approximation
      OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.contDiff_mooreRealMatrix n 1) u f (hf.of_le (by norm_num)) hK hc hB.le hBD hBH
    obtain ⟨hcA,A,hA,hAB,hAH⟩ := quaternionHessian_composition_approximation
      OAI.Analysis.PDE.Dirichlet.detRealOperator (OAI.Analysis.PDE.Dirichlet.contDiff_detRealOperator n 1) u f (hf.of_le (by norm_num)) hK hc hB.le hBD hBH
    refine ⟨hcM,hcA,M+A,by positivity,?_,?_,?_,?_⟩
    · exact fun j x hx ↦ (hMB j x hx).trans (by linarith)
    · exact fun j x hx ↦ (hAB j x hx).trans (by linarith)
    · intro j x hx y hy
      exact (hMH j x hx y hy).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg α))
    · intro j x hx y hy
      exact (hAH j x hx y hy).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg α))

end OAI.Analysis.Calculus.Coefficients
