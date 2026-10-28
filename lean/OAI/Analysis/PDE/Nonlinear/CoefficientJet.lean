import OAI.Analysis.PDE.Nonlinear.HolderComponents
import OAI.Analysis.PDE.Nonlinear.JetComposition
import OAI.Analysis.PDE.Dirichlet.C2HolderQuaternion

/-! The actual differentiated Moore coefficients have a genuine C¹,α local jet. -/

noncomputable section
open Set Filter
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore

local instance coefficientJetFirstGroup (n : ℕ) :
    NormedAddCommGroup (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance coefficientJetFirstSpace (n : ℕ) :
    NormedSpace ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance coefficientJetSecondGroup (n : ℕ) :
    NormedAddCommGroup (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance coefficientJetSecondSpace (n : ℕ) :
    NormedSpace ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance coefficientJetThirdGroup (n : ℕ) :
    NormedAddCommGroup (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance coefficientJetThirdSpace (n : ℕ) :
    NormedSpace ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance coefficientJetMatrixDGroup (n : ℕ) :
    NormedAddCommGroup (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ((Fin n × Fin 4) → (Fin n × Fin 4) → ℝ)))
local instance coefficientJetMatrixDSpace (n : ℕ) :
    NormedSpace ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ((Fin n × Fin 4) → (Fin n × Fin 4) → ℝ)))

theorem exists_moore_coefficient_jet {n : ℕ} (hn : 3 ≤ n * 4) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ)
    (hu : ContDiff ℝ 3 u) (hf : ContDiff ℝ 2 f) (x₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
    (hPDE : ∀ᶠ x in 𝓝 x₀, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hPD : ∀ᶠ x in 𝓝 x₀, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef) :
    ∃ g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ,
      ContDiff ℝ 1 g ∧ g =ᶠ[𝓝 x₀] (fun x => OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)) ∧
      ∃ (A : OAI.Analysis.Normed.Function.Holder.HolderMap (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) α)
        (DA : OAI.Analysis.Normed.Function.Holder.HolderMap (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
          (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) α),
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = g x) ∧ (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value DA x = fderiv ℝ g x) := by
  obtain ⟨r, hr, C, hC, hh⟩ := moore_third_derivative_holder hn hα hα1 u f hu hf x₀ hPDE hPD
  have hHess : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    (hu.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
  obtain ⟨H, hH, _, hHeq, V, D, hV, hD⟩ := exists_C1_holder_extension
    (fderiv ℝ (fderiv ℝ u)) x₀ hHess.contDiffAt hr hα.le hα1.le hC.le hh
  let G := fun T : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ =>
    OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots T)
  have hG : ContDiff ℝ 2 G :=
    (OAI.Analysis.PDE.Dirichlet.contDiff_mooreRealMatrix n 2).comp (OAI.Analysis.PDE.Dirichlet.secondJetToQuaternionCLM OAI.Analysis.Calculus.Quaternion.fourSlots).contDiff
  obtain ⟨A, DA, hA, hDA⟩ := exists_C1_holder_composition hα.le H hH G hG V D hV hD
  refine ⟨G ∘ H, (hG.of_le (by norm_num)).comp hH, ?_, A, DA, hA, hDA⟩
  filter_upwards [hHeq] with x hx
  change G (H x) = _
  rw [hx]
  rfl

end OAI.Analysis.PDE.Nonlinear
