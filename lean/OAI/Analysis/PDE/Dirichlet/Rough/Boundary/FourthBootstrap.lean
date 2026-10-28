import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.DifferentiatedEquation

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

local instance roughFourthBootstrapFirstGroup (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedAddCommGroup (V →L[ℝ] ℝ) := inferInstance
local instance roughFourthBootstrapFirstSpace (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedSpace ℝ (V →L[ℝ] ℝ) := inferInstance
local instance roughFourthBootstrapSecondGroup (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance
local instance roughFourthBootstrapSecondSpace (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) := inferInstance

/-- A C³ representative, the nonlinear elliptic equation, and only C²
regularity of twice-tangential derivatives give C⁴ on the closed patch.
In applications the C³ representative comes from the preceding C²→C³
normal bootstrap and finite reflection, not an extra smoothness premise. -/
theorem contDiffOn_four_of_second_tangents
    (F : NonlinearJet E → ℝ) (hF : ContDiff ℝ 2 F)
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    {S : Set E} (hS : UniqueDiffOn ℝ S) {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    (ht : ∀ v, ℓ v = 0 → ∀ w, ℓ w = 0 →
      ContDiffOn ℝ 2 (constantDirectional (constantDirectional f v) w) S)
    (he : ∀ x ∈ S, F (nonlinearTwoJet f x) = 0)
    (hell : ∀ x ∈ S, fderiv ℝ F (nonlinearTwoJet f x) (0,ℓ.smulRight ℓ) ≠ 0) :
    ContDiffOn ℝ 4 f S := by
  have ht3 (v : E) (hv : ℓ v = 0) : ContDiffOn ℝ 3 (constantDirectional f v) S := by
    have hg : ContDiff ℝ 2 (constantDirectional f v) :=
      (hf.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
    apply contDiffOn_of_nonlinear_equation_and_tangents
      (differentiatedResidual F f v) ℓ ν hν hS (k := 1) (by norm_num)
      hg.contDiffOn (fun x _ ↦ hg.contDiffAt) (ht v hv)
    · intro x hx
      exact (contDiff_differentiatedResidual hF hf v).contDiffAt
    · exact fun x hx ↦ differentiatedResidual_equation hF hf hS he v hx
    · intro x hx
      rw [differentiatedResidual_normal_symbol hF hf]
      exact hell x hx
  exact contDiffOn_of_nonlinear_equation_and_tangents F ℓ ν hν hS
    (k := 2) (by norm_num) hf.contDiffOn (fun x _ ↦ hf.contDiffAt.of_le (by norm_num))
    ht3 (fun x _ ↦ hF.contDiffAt) he hell

end OAI.Analysis.PDE.Dirichlet
