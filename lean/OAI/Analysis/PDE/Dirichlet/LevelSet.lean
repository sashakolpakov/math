import OAI.Analysis.PDE.Dirichlet.Boundary.Normal
import OAI.Analysis.PDE.Dirichlet.Derivative
import Mathlib.Analysis.Calculus.Implicit

open Filter Set
open scoped Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem real_linear_form_range_top (g : E →L[ℝ] ℝ) (hg : g ≠ 0) : g.range = ⊤ := by
  obtain ⟨w, hw⟩ := linear_form_exists_negative g hg
  apply LinearMap.range_eq_top.mpr
  intro t
  refine ⟨(t / g w) • w, ?_⟩
  change g ((t / g w) • w) = t
  simp only [map_smul, smul_eq_mul]
  exact div_mul_cancel₀ _ hw.ne

/-- The derivative of a function vanishing on a regular level set kills every
tangent vector. The tangent parametrization is supplied by the implicit
function theorem, rather than assumed. -/
theorem level_set_derivative_zero [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {r : E → ℝ} {r' : E →L[ℝ] ℝ} {f : E → F} {f' : E →L[ℝ] F} {x v : E}
    (hr : HasStrictFDerivAt r r' x) (hrne : r' ≠ 0)
    (hf : HasFDerivAt f f' x)
    (hzero : ∀ᶠ y in 𝓝 x, r y = r x → f y = 0) (hv : r' v = 0) : f' v = 0 := by
  let hsurj := real_linear_form_range_top r' hrne
  let I : r'.ker → E := hr.implicitFunction r r' hsurj (r x)
  have hIx : I 0 = x := hr.implicitFunction_apply_image hsurj
  have hI : HasFDerivAt I r'.ker.subtypeL 0 := (hr.to_implicitFunction hsurj).hasFDerivAt
  have hIt : Tendsto I (𝓝 0) (𝓝 x) := hIx ▸ hI.continuousAt.tendsto
  have hp : Tendsto (fun z : r'.ker ↦ (r x, z)) (𝓝 0) (𝓝 (r x, 0)) :=
    tendsto_const_nhds.prodMk_nhds tendsto_id
  have hlevel : ∀ᶠ z : r'.ker in 𝓝 0, r (I z) = r x :=
    hp.eventually (hr.map_implicitFunction_eq hsurj)
  have heq : (fun z : r'.ker ↦ f (I z)) =ᶠ[𝓝 0] (fun _ ↦ (0 : F)) := by
    filter_upwards [hIt.eventually hzero, hlevel] with z hz hl
    exact hz hl
  have hfI : HasFDerivAt f f' (I 0) := by simpa only [hIx] using hf
  have hcomp : HasFDerivAt (fun z ↦ f (I z)) (f'.comp r'.ker.subtypeL) 0 := hfI.comp 0 hI
  have hder : f'.comp r'.ker.subtypeL = 0 := by
    rw [← hcomp.fderiv, heq.fderiv_eq]
    simp
  have heval := congrArg (fun L : r'.ker →L[ℝ] F ↦ L ⟨v, hv⟩) hder
  simpa using heval

theorem level_set_gradient_factor [CompleteSpace E]
    {r u : E → ℝ} {x : E}
    (hr : HasStrictFDerivAt r (fderiv ℝ r x) x) (hrne : fderiv ℝ r x ≠ 0)
    (hu : DifferentiableAt ℝ u x)
    (hzero : ∀ᶠ y in 𝓝 x, r y = r x → u y = 0) :
    ∃ a : ℝ, fderiv ℝ u x = a • fderiv ℝ r x := by
  apply linear_form_factor_of_kernel _ _ hrne
  intro v hv
  exact level_set_derivative_zero hr hrne hu.hasFDerivAt hzero hv

/-- On the tangent space of a regular zero boundary, the real Hessians obey
the same proportionality as the gradients. No boundary chart is an input. -/
theorem level_set_tangent_hessian [CompleteSpace E]
    {r u : E → ℝ} {x v z : E} {a : ℝ}
    (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 2 u) (hrne : fderiv ℝ r x ≠ 0)
    (hzero : ∀ᶠ y in 𝓝 x, r y = r x → u y = 0)
    (hfactor : fderiv ℝ u x = a • fderiv ℝ r x)
    (hv : fderiv ℝ r x v = 0) (hz : fderiv ℝ r x z = 0) :
    fderiv ℝ (fderiv ℝ u) x v z = a * fderiv ℝ (fderiv ℝ r) x v z := by
  obtain ⟨w, hw⟩ := linear_form_exists_negative (fderiv ℝ r x) hrne
  have hDr (q : E) : ContDiff ℝ 1 (directionalDerivative r q) :=
    contDiff_directionalDerivative hr (by norm_num) q
  have hDu (q : E) : ContDiff ℝ 1 (directionalDerivative u q) :=
    contDiff_directionalDerivative hu (by norm_num) q
  have hlocal : ∀ᶠ y in 𝓝 x, ∀ᶠ p in 𝓝 y, r p = r x → u p = 0 := by
    obtain ⟨U, hU, hUopen, hxU⟩ := mem_nhds_iff.mp hzero
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    exact Filter.mem_of_superset (hUopen.mem_nhds hy) hU
  have hnonzero : ∀ᶠ y in 𝓝 x, directionalDerivative r w y ≠ 0 :=
    ((hDr w).continuous.tendsto x).eventually (eventually_ne_nhds hw.ne)
  have hcross : ∀ᶠ y in 𝓝 x, r y = r x →
      directionalDerivative r w y * directionalDerivative u z y -
        directionalDerivative u w y * directionalDerivative r z y = 0 := by
    filter_upwards [hlocal, hnonzero] with y hy hyn
    intro hry
    have hyrne : fderiv ℝ r y ≠ 0 := by
      intro heq
      exact hyn (by simp [directionalDerivative, heq])
    have hzy : ∀ᶠ p in 𝓝 y, r p = r y → u p = 0 := by
      simpa only [hry] using hy
    obtain ⟨c, hc⟩ := level_set_gradient_factor (hr.hasStrictFDerivAt (by norm_num))
      hyrne ((hu.differentiable (by norm_num)) y) hzy
    simp only [directionalDerivative, hc, smul_apply, smul_eq_mul]
    ring
  have hprod := (((hDr w).differentiable (by norm_num) x).hasFDerivAt.mul
    ((hDu z).differentiable (by norm_num) x).hasFDerivAt).sub
    (((hDu w).differentiable (by norm_num) x).hasFDerivAt.mul
      ((hDr z).differentiable (by norm_num) x).hasFDerivAt)
  have hd := level_set_derivative_zero (hr.hasStrictFDerivAt (by norm_num))
    hrne hprod hcross hv
  have hrr (p q : E) : fderiv ℝ (directionalDerivative r q) x p =
      fderiv ℝ (fderiv ℝ r) x p q := directionalDerivative_twice hr p q x
  have huu (p q : E) : fderiv ℝ (directionalDerivative u q) x p =
      fderiv ℝ (fderiv ℝ u) x p q := directionalDerivative_twice hu p q x
  have huz : directionalDerivative u z x = 0 := by
    simp only [directionalDerivative, hfactor, smul_apply, smul_eq_mul, hz, mul_zero]
  have huw : directionalDerivative u w x = a * fderiv ℝ r x w := by
    simp only [directionalDerivative, hfactor, smul_apply, smul_eq_mul]
  simp only [sub_apply, add_apply, smul_apply,
    smul_eq_mul, hrr, huu] at hd
  rw [huz, huw] at hd
  simp only [directionalDerivative, hz, zero_mul, add_zero] at hd
  have heq : fderiv ℝ r x w * (fderiv ℝ (fderiv ℝ u) x v z -
      a * fderiv ℝ (fderiv ℝ r) x v z) = 0 := by nlinarith [hd]
  exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left hw.ne)

end OAI.Analysis.PDE.Dirichlet
