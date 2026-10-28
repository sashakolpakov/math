import OAI.Analysis.PDE.Dirichlet.Fourth.FieldBackground
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.PathBounds

noncomputable section
open Set Filter Module
open scoped Topology ContDiff Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.Analysis.PDE.Elliptic OAI.Analysis.PDE.Schauder OAI.LinearAlgebra.Moore

variable {n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "E" => CoordinateSpace n 4

local instance closedEquationContinuityFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance closedEquationContinuityFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance closedEquationContinuitySecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance closedEquationContinuitySecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance closedEquationContinuityMatrixGroup :
    NormedAddCommGroup (Matrix (Fin n) (Fin n) (Quaternion ℝ)) := inferInstance
local instance closedEquationContinuityMatrixSpace :
    NormedSpace ℝ (Matrix (Fin n) (Fin n) (Quaternion ℝ)) := inferInstance

private theorem continuous_moore_linearization_of_C2
    (A : E → Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hA : Continuous A)
    (q : E → ℝ) (hq : ContDiff ℝ 2 q) : Continuous (mooreLinearization A q) := by
  have hHq : Continuous (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots q) :=
    continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hq
  have hc := (OAI.LinearAlgebra.Moore.continuous_mooreDifferential n).comp (hA.prodMk hHq)
  change Continuous (fun x => OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots q x))
  exact hc

private theorem SmoothPathSolution.second_field_equation_interior
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P} {r B₀ F₀ F₁ : E → ℝ}
    (s : SmoothPathSolution e lat r B₀ F₀ F₁)
    (hr : Continuous r) (hB₀ : ContDiff ℝ 4 B₀)
    (hF₀ : ContDiff ℝ 2 F₀) (hF₁ : ContDiff ℝ 2 F₁)
    (T W : E → E) (hT : ContDiff ℝ 3 T) (hW : ContDiff ℝ 2 W)
    {x : E} (hx : r x < 0) :
    mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y => B₀ y+s.u y))
      (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) W) x =
    mooreSecondBackgroundForcing (fun y => B₀ y+s.u y) B₀
      (densityPath F₀ F₁ s.t) T W x := by
  have hsource := moore_second_background_equation (fun y => B₀ y+s.u y) B₀
    (densityPath F₀ F₁ s.t) T W (hB₀.add s.smooth) hB₀ hT hW
    ((contDiff_densityPath hF₀ hF₁ s.t).of_le (by norm_num)) x (by
      filter_upwards [(isOpen_lt hr continuous_const).mem_nhds hx] with y hy
      exact s.equation y hy)
  have hsub : (fun y => B₀ y+s.u y-B₀ y) = s.u := by funext y; ring
  rw [hsub] at hsource
  exact hsource

/-- The twice-field equation extends to the entire closed domain by
continuity. The fields need not be tangent, so this also gives the normal
equations required for fourth-order recovery at the boundary. -/
theorem SmoothPathSolution.second_field_equation_on_closed_sublevel
    {e : E ≃L[ℝ] P × V} {lat : Basis ι ℝ P} {r B₀ F₀ F₁ : E → ℝ}
    (s : SmoothPathSolution e lat r B₀ F₀ F₁)
    (hr : ContDiff ℝ 1 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hB₀ : ContDiff ℝ 5 B₀) (hF₀ : ContDiff ℝ 3 F₀) (hF₁ : ContDiff ℝ 3 F₁)
    (T W : E → E) (hT : ContDiff ℝ 4 T) (hW : ContDiff ℝ 3 W) :
    ∀ x, r x ≤ 0 →
      OAI.Analysis.PDE.Elliptic.ellipticTrace
        (fun y => detRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun z => B₀ z+s.u z) y))
        (OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) W) x =
      mooreSecondBackgroundForcing (fun y => B₀ y+s.u y) B₀
        (densityPath F₀ F₁ s.t) T W x := by
  let ψ := fun y => B₀ y+s.u y
  let q := OAI.Analysis.PDE.Elliptic.fieldDerivative (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) W
  have hψ : ContDiff ℝ 4 ψ := (hB₀.of_le (by norm_num)).add s.smooth
  have hq₁ : ContDiff ℝ 3 (OAI.Analysis.PDE.Elliptic.fieldDerivative s.u T) :=
    OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative s.smooth (hT.of_le (by norm_num)) (by norm_num)
  have hq : ContDiff ℝ 2 q :=
    OAI.Analysis.PDE.Elliptic.contDiff_fieldDerivative hq₁ (hW.of_le (by norm_num)) (by norm_num)
  have hleft : Continuous (mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) q) :=
    continuous_moore_linearization_of_C2 _
      (continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (hψ.of_le (by norm_num))) q hq
  have hright : Continuous (mooreSecondBackgroundForcing ψ B₀
      (densityPath F₀ F₁ s.t) T W) :=
    (contDiff_mooreSecondBackgroundForcing ψ B₀ _ T W hψ hB₀
      ((hF₀.const_smul (1-s.t)).add (hF₁.const_smul s.t)) hT hW).continuous
  have heq : ∀ x, r x ≤ 0 →
      mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) q x =
        mooreSecondBackgroundForcing ψ B₀ (densityPath F₀ F₁ s.t) T W x := by
    apply equality_on_regular_sublevel_of_interior hr hreg hleft hright
    intro x hx
    exact s.second_field_equation_interior hr.continuous (hB₀.of_le (by norm_num))
      (hF₀.of_le (by norm_num)) (hF₁.of_le (by norm_num)) T W
      (hT.of_le (by norm_num)) (hW.of_le (by norm_num))
      (neg_of_mem_interior_regular_sublevel hreg hx)
  intro x hx
  exact (detRealOperator_linearization _ hq x).trans (heq x hx)

end OAI.Analysis.PDE.Dirichlet
