import OAI.Analysis.PDE.Dirichlet.NonlinearParameterJetActual
import OAI.Analysis.PDE.Dirichlet.Rough.FixedDomainSmooth

noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.PDE.Dirichlet

attribute [local instance] linearizedFirstGroup linearizedFirstSpace
  linearizedSecondGroup linearizedSecondSpace

variable {m : ℕ} {Z E : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "W" => EuclideanSpace ℝ (Fin m)

/-- The fixed-halfspace bootstrap applies jointly to external parameters
and spatial variables. Only the spatial normal symbol must be nonzero;
no ellipticity in the new parameter directions is required. The equation
uses the actual first and second derivatives of the joint function. -/
theorem contDiffOn_infty_parameter_halfspace_of_mixed_tangents
    (p : W →L[ℝ] Z) (q : W →L[ℝ] E) (i : E →L[ℝ] W)
    (F : Z × NonlinearJet E → ℝ) (hF : ContDiff ℝ ∞ F)
    (ℓ : W →L[ℝ] ℝ) (k : E →L[ℝ] ℝ) (hk : ℓ.comp i = k)
    (ν : W) (hν : ℓ ν = 1)
    {O : Set W} (hO : IsOpen O) {f : W → ℝ} (hf : ContDiff ℝ 2 f)
    (hi : ∀ x ∈ O, 0 < ℓ x → ContDiffAt ℝ ∞ f x)
    (ht : ∀ (N : ℕ) (v : Fin N → ℓ.ker), ContDiffOn ℝ 2
      (fun z ↦ iteratedFDeriv ℝ N (fun t : ℓ.ker ↦ f (z+(t:W))) 0 v)
      ({x | 0 ≤ ℓ x} ∩ O))
    (he : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ O),
      F (parameterJetProjection p q i (nonlinearTwoJet f x)) = 0)
    (hell : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ O),
      fderiv ℝ (fun a => F (p x,a))
        (parameterJetProjection p q i (nonlinearTwoJet f x)).2
        (0,k.smulRight k) ≠ 0) :
    ContDiffOn ℝ ∞ f ({x | 0 ≤ ℓ x} ∩ O) := by
  apply contDiffOn_infty_halfspace_of_mixed_tangents
    (parameterResidual p q i F) (contDiff_parameterResidual p q i hF)
    ℓ ν hν hO hf hi ht
  · intro x hx
    exact he x hx
  · intro x hx
    have hdiff : DifferentiableAt ℝ F
        (parameterJetProjection p q i (nonlinearTwoJet f x)) :=
      hF.differentiable (by simp) _
    rw [parameterResidual_normal_symbol_slice p q i F (nonlinearTwoJet f x) ℓ k hk hdiff]
    exact hell x hx

end OAI.Analysis.PDE.Dirichlet
