import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.ParameterJets
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffAt_succ_of_fderiv_field {f : E → F} {x : E} {k : ℕ}
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y)
    (hD : ContDiffAt ℝ k (fderiv ℝ f) x) : ContDiffAt ℝ (k+1) f x := by
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  exact ⟨fderiv ℝ f, ⟨{y | DifferentiableAt ℝ f y}, hf, fun y hy ↦ hy.hasFDerivAt⟩, hD⟩

theorem contDiffAt_of_hessian_field {f : E → F} {x : E} {k : ℕ}
    (hf : ContDiffAt ℝ 2 f x)
    (hD : ContDiffAt ℝ k (fderiv ℝ (fderiv ℝ f)) x) :
    ContDiffAt ℝ (k+2) f x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  have hD1 : ContDiffAt ℝ (k+1) (fderiv ℝ f) x := contDiffAt_succ_of_fderiv_field
    ((hd.eventually (by norm_num)).mono (fun y hy ↦ hy.differentiableAt (by norm_num))) hD
  exact contDiffAt_succ_of_fderiv_field
    ((hf.eventually (by norm_num)).mono (fun y hy ↦ hy.differentiableAt (by norm_num))) hD1

def constantDirectional (f : E → ℝ) (v : E) (x : E) : ℝ := fderiv ℝ f x v

theorem fderiv_constantDirectional_apply {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (v w : E) :
    fderiv ℝ (constantDirectional f v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : fderiv ℝ (constantDirectional f v) x =
      (ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ f) x) :=
    ((ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp x hd.hasFDerivAt).fderiv
  rw [he]
  rfl

def normalJetRemainder (ℓ : E →L[ℝ] ℝ) (ν : E) (f : E → ℝ) (x : E) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) x - (fderiv ℝ (fderiv ℝ f) x ν ν) • ℓ.smulRight ℓ

theorem normalJetRemainder_apply (ℓ : E →L[ℝ] ℝ) (ν : E) (f : E → ℝ) (x v w : E) :
    normalJetRemainder ℓ ν f x v w =
      fderiv ℝ (fderiv ℝ f) x (v - ℓ v • ν) w +
        ℓ v * fderiv ℝ (fderiv ℝ f) x ν (w - ℓ w • ν) := by
  simp only [normalJetRemainder, sub_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, map_sub, map_smul, smul_eq_mul]
  ring

/-- The Hessian with its pure normal component removed gains regularity from
the tangential derivatives, with no regularity assumption on the missing
normal component. -/
theorem contDiffAt_normalJetRemainder [FiniteDimensional ℝ E]
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    {f : E → ℝ} {x : E} {k : ℕ} (hf : ContDiffAt ℝ 2 f x)
    (ht : ∀ v, ℓ v = 0 → ContDiffAt ℝ (k+1) (constantDirectional f v) x) :
    ContDiffAt ℝ k (normalJetRemainder ℓ ν f) x := by
  rw [← contDiffWithinAt_univ]
  apply contDiffWithinAt_clm_apply.mpr
  intro v
  apply contDiffWithinAt_clm_apply.mpr
  intro w
  have hv : ℓ (v - ℓ v • ν) = 0 := by simp [hν]
  have hw : ℓ (w - ℓ w • ν) = 0 := by simp [hν]
  have ha : ContDiffAt ℝ k (fun y ↦ fderiv ℝ (constantDirectional f (v - ℓ v • ν)) y w) x :=
    ((ht _ hv).fderiv_right (by simp)).clm_apply contDiffAt_const
  have hb : ContDiffAt ℝ k (fun y ↦ fderiv ℝ (constantDirectional f (w - ℓ w • ν)) y ν) x :=
    ((ht _ hw).fderiv_right (by simp)).clm_apply contDiffAt_const
  have he : (fun y ↦ normalJetRemainder ℓ ν f y v w) =ᶠ[𝓝 x]
      (fun y ↦ fderiv ℝ (constantDirectional f (v - ℓ v • ν)) y w +
        ℓ v * fderiv ℝ (constantDirectional f (w - ℓ w • ν)) y ν) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    rw [normalJetRemainder_apply, fderiv_constantDirectional_apply hy,
      fderiv_constantDirectional_apply hy, (hy.isSymmSndFDerivAt (by norm_num)).eq (v - ℓ v • ν) w]
  exact (ha.add (contDiffAt_const.mul hb)).congr_of_eventuallyEq he

end OAI.Analysis.PDE.Dirichlet
