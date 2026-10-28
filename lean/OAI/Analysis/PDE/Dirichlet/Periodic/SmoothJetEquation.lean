import OAI.Analysis.PDE.Dirichlet.Periodic.SmoothJet
import OAI.Analysis.PDE.Weak.PeriodicDirichletSublevel
import OAI.Analysis.Normed.Function.Holder.C2HolderEquationLimit
import OAI.Analysis.PDE.Dirichlet.Continuity

open Set Filter Module
open scoped Topology ContDiff Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

theorem continuous_equality_on_regular_closed_sublevel {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r f g : E → ℝ} (hr : ContDiff ℝ 1 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hf : Continuous f) (hg : Continuous g)
    (heq : ∀ x, r x < 0 → f x = g x) :
    ∀ x, r x ≤ 0 → f x = g x := by
  have hcl := OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular r hr hreg
  intro x hx
  have hxcl : x ∈ closure ({x | r x < 0} : Set E) := by
    rw [hcl]
    exact hx
  exact closure_minimal (s := {x | r x < 0})
    (t := {x | f x = g x}) heq (isClosed_eq hf hg) hxcl

/-- A genuine interior linearized Moore equation holds at the boundary
as well, by continuity of the actual Hessians. -/
theorem mooreLinearization_on_closed_sublevel {n : ℕ}
    {r ψ u F : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 1 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hψ : ContDiff ℝ 2 ψ) (hu : ContDiff ℝ 2 u) (hF : Continuous F)
    (heq : ∀ x, r x < 0 → mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) u x = F x) :
    ∀ x, r x ≤ 0 → mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) u x = F x := by
  have hp : Continuous (fun x : CoordinateSpace n 4 ↦
      (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x, quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)) :=
    (continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hψ).prodMk
      (continuous_quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots hu)
  have hc : Continuous (mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) u) :=
    (OAI.LinearAlgebra.Moore.continuous_mooreDifferential n).comp
      (f := fun x : CoordinateSpace n 4 ↦
        (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x, quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)) hp
  exact continuous_equality_on_regular_closed_sublevel hr hreg hc hF heq

theorem mooreDet_on_closed_sublevel {n : ℕ}
    {r u F : CoordinateSpace n 4 → ℝ}
    (hr : ContDiff ℝ 1 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hu : ContDiff ℝ 2 u) (hF : Continuous F)
    (heq : ∀ x, r x < 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = F x) :
    ∀ x, r x ≤ 0 → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = F x :=
  continuous_equality_on_regular_closed_sublevel hr hreg (continuous_mooreHessian OAI.Analysis.Calculus.Quaternion.fourSlots hu) hF heq

/-- The closed equation for a smooth solution is the equation of its
genuine C²,α jet, not merely an identity for a chosen representative. -/
theorem mooreLinearization_C2Holder_on_closed_sublevel {n : ℕ}
    {r ψ u F : CoordinateSpace n 4 → ℝ}
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hr : ContDiff ℝ 1 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hψ : ContDiff ℝ 2 ψ) (hu : ContDiff ℝ 2 u) (hF : Continuous F)
    (heq : ∀ x, r x < 0 → mooreLinearization (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ) u x = F x)
    (v : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α)
    (hv : ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative v x = fderiv ℝ (fderiv ℝ u) x) :
    ∀ x : {x | r x ≤ 0}, OAI.LinearAlgebra.Moore.mooreDifferential n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value (quaternionHessianField hΩD α OAI.Analysis.Calculus.Quaternion.fourSlots v) x) = F x := by
  intro x
  rw [quaternionHessianField_eq_of_secondDerivative_eq OAI.Analysis.Calculus.Quaternion.fourSlots v u x (hv x)]
  exact mooreLinearization_on_closed_sublevel hr hreg hψ hu hF heq x x.property

end OAI.Analysis.PDE.Dirichlet
