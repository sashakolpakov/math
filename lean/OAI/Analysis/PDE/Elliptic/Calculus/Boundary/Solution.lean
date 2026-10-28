import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.CoordinateSource

/-! Explicit varying data for the nonlinear boundary third-derivative
estimate. No third-derivative norm or differentiated PDE is assumed. -/

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Schauder

variable {n m : ℕ}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local notation "X" => EuclideanSpace ℝ (Fin m)
local instance boundarySolutionFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance boundarySolutionFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance boundarySolutionSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance boundarySolutionSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance boundarySolutionEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance boundarySolutionEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance

structure BoundaryLogSolution (e : X ≃ₗᵢ[ℝ] E) (k : Fin m)
    {Ω K : Set E} (hΩK : Ω ⊆ K) (S : Set E) (G : E → E) (B₀ : E → ℝ)
    (α R N Z ell Λ : ℝ) where
  u : E → ℝ
  f : E → ℝ
  U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α
  A : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E) α
  W : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] ℝ) α
  smooth : ContDiff ℝ 4 u
  norm_U : ‖U‖ ≤ R
  norm_A : ‖A‖ ≤ N
  norm_W : ‖W‖ ≤ Z
  value_U : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x
  first_U : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x
  second_U : ∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x
  value_A : ∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)
  value_W : ∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value W x = (f x)⁻¹ • fderiv ℝ f x
  source_differentiable : ∀ x ∈ S, DifferentiableAt ℝ f (G x)
  equation : ∀ x ∈ S,
    (fun z => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u z)) =ᶠ[𝓝 (G x)] f
  lower : ∀ x ∈ K, ∀ v, ell*‖v‖^2 ≤ inner ℝ v (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) v)
  upper : ∀ x ∈ K, ∀ v, inner ℝ v (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) v) ≤ Λ*‖v‖^2
  trace : ∀ x ∈ Metric.ball (0 : X) (1/2), x k = 0 → u (G (e x)) = B₀ (G (e x))

namespace BoundaryLogSolution

variable {e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4} {k : Fin m}
  {Ω K S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} {hΩK : Ω ⊆ K}
  {G : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4} {B₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ}
  {α R N Z ell Λ : ℝ}

def flatFunction (p : BoundaryLogSolution e k hΩK S G B₀ α R N Z ell Λ) :
    EuclideanSpace ℝ (Fin m) → ℝ :=
  ((fun y => p.u y-B₀ y) ∘ G) ∘ e

theorem flatFunction_contDiff (p : BoundaryLogSolution e k hΩK S G B₀ α R N Z ell Λ)
    (hG : ContDiff ℝ 4 G) (hB₀ : ContDiff ℝ 4 B₀) :
    ContDiff ℝ 4 p.flatFunction :=
  ((p.smooth.sub hB₀).comp hG).comp e.contDiff

end BoundaryLogSolution
end OAI.Analysis.PDE.Elliptic
