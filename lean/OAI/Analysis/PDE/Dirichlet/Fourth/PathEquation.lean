import OAI.Analysis.PDE.Dirichlet.Fourth.FieldBackground
import OAI.Analysis.PDE.Dirichlet.Path.Solution

/-! The actual twice-tangential derivative is an admissible classical
solution of the differentiated zero-Dirichlet equation. -/
noncomputable section
open Set Module Filter
open scoped ContDiff Topology
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.Analysis.PDE.Elliptic OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4

theorem SmoothPathSolution.second_tangent_classical_equation
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P} {r B₀ F₀ F₁ : E → ℝ}
    (s : SmoothPathSolution e lat r B₀ F₀ F₁)
    (hr : ContDiff ℝ 1 r) (hreg : ∀ x, r x=0 → fderiv ℝ r x ≠ 0)
    (hB₀ : ContDiff ℝ 4 B₀) (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (T S : E → E) (hT : ContDiff ℝ 3 T) (hS : ContDiff ℝ 2 S)
    (hTp : LatticePeriodic e lat T) (hSp : LatticePeriodic e lat S)
    (hTtan : ∀ x, r x=0 → fderiv ℝ r x (T x)=0)
    (hStan : ∀ x, r x=0 → fderiv ℝ r x (S x)=0) :
    ContDiff ℝ 2 (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S) ∧
      LatticePeriodic e lat (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S) ∧
      (∀ x, r x=0 → OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S x=0) ∧
      (∀ x, r x<0 →
        mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y))
          (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) S) x =
        mooreSecondBackgroundForcing (fun y => B₀ y+s.u y) B₀
          (densityPath F₀ F₁ s.t) T S x) := by
  refine ⟨OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative (OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative s.smooth hT (by norm_num))
      hS (by norm_num), (s.periodic.fieldDerivative hTp).fieldDerivative hSp, ?_, ?_⟩
  · intro x hx
    exact twice_fieldDerivative_zero_on_level hr (s.smooth.of_le (by norm_num))
      (hT.of_le (by norm_num)) hreg s.zero hTtan hStan hx
  · intro x hx
    have he := moore_second_background_equation (fun y => B₀ y+s.u y) B₀
      (densityPath F₀ F₁ s.t) T S (hB₀.add s.smooth) hB₀ hT hS
      ((contDiff_densityPath hF₀ hF₁ s.t).of_le (by norm_num)) x
      (show ∀ᶠ y in 𝓝 x,
        OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z => B₀ z+s.u z) y) =
          densityPath F₀ F₁ s.t y from by
        filter_upwards [(isOpen_lt hr.continuous continuous_const).mem_nhds hx] with y hy
        exact s.equation y hy)
    have hsub : (fun y => B₀ y+s.u y-B₀ y) = s.u := by funext y; ring
    simpa only [hsub] using he

end OAI.Analysis.PDE.Dirichlet
