import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.DifferentiatedEquation

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

local instance higherBootstrapFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance higherBootstrapFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance higherBootstrapSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance higherBootstrapSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

def iteratedConstantDirectional (f : E → ℝ) : List E → E → ℝ
  | [] => f
  | v :: vs => iteratedConstantDirectional (constantDirectional f v) vs

omit [FiniteDimensional ℝ E] in
theorem contDiff_differentiatedResidual_order {k : ℕ}
    {F : NonlinearJet E → ℝ} {f : E → ℝ}
    (hF : ContDiff ℝ (k+1) F) (hf : ContDiff ℝ (k+2) f) (v : E) :
    ContDiff ℝ k (differentiatedResidual F f v) := by
  exact ((hF.fderiv_right (m := k) (by norm_cast)).comp
    ((contDiff_nonlinearTwoJet hf).comp contDiff_fst.fst)).clm_apply
      ((contDiff_const.prodMk contDiff_fst.snd).prodMk contDiff_snd)

/-- Finite-order nonlinear normal recovery. At order k, only two
derivatives of the (k+1)-fold tangential derivatives are needed. The
proof differentiates the genuine equation and inducts on k; it does not
assume higher normal derivatives or an elliptic regularity oracle. -/
theorem contDiffOn_higher_of_iterated_tangents (k : ℕ)
    (F : NonlinearJet E → ℝ) (hF : ContDiff ℝ (k+1) F)
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    {S : Set E} (hS : UniqueDiffOn ℝ S) {f : E → ℝ}
    (hf : ContDiff ℝ (k+2) f)
    (ht : ∀ vs : List E, vs.length = k+1 → (∀ v ∈ vs, ℓ v = 0) →
      ContDiffOn ℝ 2 (iteratedConstantDirectional f vs) S)
    (he : ∀ x ∈ S, F (nonlinearTwoJet f x) = 0)
    (hell : ∀ x ∈ S, fderiv ℝ F (nonlinearTwoJet f x) (0,ℓ.smulRight ℓ) ≠ 0) :
    ContDiffOn ℝ (k+3) f S := by
  induction k generalizing F f with
  | zero =>
      apply contDiffOn_of_nonlinear_equation_and_tangents F ℓ ν hν hS
        (k := 1) (by norm_num) hf.contDiffOn (fun x hx ↦ hf.contDiffAt)
      · intro v hv
        exact ht [v] rfl (by simpa using hv)
      · exact fun x hx ↦ hF.contDiffAt
      · exact he
      · exact hell
  | succ k ih =>
      have hf3 : ContDiff ℝ 3 f := hf.of_le (by exact_mod_cast (by omega : 3 ≤ k+1+2))
      have hF2 : ContDiff ℝ 2 F := hF.of_le (by exact_mod_cast (by omega : 2 ≤ k+1+1))
      have ht' (v : E) (hv : ℓ v = 0) :
          ContDiffOn ℝ (k+3) (constantDirectional f v) S := by
        have hg : ContDiff ℝ (k+2) (constantDirectional f v) :=
          (hf.fderiv_right (m := k+2) (by norm_cast)).clm_apply contDiff_const
        have hG : ContDiff ℝ (k+1) (differentiatedResidual F f v) :=
          contDiff_differentiatedResidual_order hF hf v
        apply ih (differentiatedResidual F f v) hG hg
        · intro vs hlen hvs
          exact ht (v::vs) (by simp only [List.length_cons,hlen])
            (by intro w hw; rcases List.mem_cons.mp hw with rfl | hw; exact hv; exact hvs w hw)
        · exact fun x hx ↦ differentiatedResidual_equation hF2 hf3 hS he v hx
        · intro x hx
          rw [differentiatedResidual_normal_symbol hF2 hf3]
          exact hell x hx
      apply contDiffOn_of_nonlinear_equation_and_tangents F ℓ ν hν hS
        (k := k+2) (by omega) hf.contDiffOn (fun x hx ↦ hf3.contDiffAt.of_le (by norm_num))
      · exact ht'
      · exact fun x hx ↦ hF.contDiffAt
      · exact he
      · exact hell

end OAI.Analysis.PDE.Dirichlet
