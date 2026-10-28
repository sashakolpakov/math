import OAI.Geometry.Nikodym.Jacobi.Exponential

noncomputable section
namespace OAI.Geometry.Nikodym

open Set
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem radialExponentialFlow_unit (κ t : ℝ) {e : E} (he : ‖e‖ = 1) :
    radialExponentialFlow κ e t = (curvatureCos κ t,curvatureSin κ t • e) := by
  let F := radialExponentialFlow κ e
  let a : ℝ → ℝ := fun s => (F s).1
  let J : ℝ → E := fun s => (F s).2
  let q : ℝ → ℝ := fun s => ⟪e,J s⟫
  have hee : ⟪e,e⟫ = (1:ℝ) := by simp [he]
  have ha (s : ℝ) : HasDerivAt a ((-κ) * q s) s := by
    simpa [a,q,J,F,radialGenerator_apply] using!
      (hasDerivAt_radialExponentialFlow κ e s).hasFDerivAt.fst.hasDerivAt
  have hJ (s : ℝ) : HasDerivAt J (a s • e) s := by
    simpa [a,J,F,radialGenerator_apply] using!
      (hasDerivAt_radialExponentialFlow κ e s).hasFDerivAt.snd.hasDerivAt
  have hq (s : ℝ) : HasDerivAt q (a s) s := by
    simpa only [q,inner_zero_left,add_zero,real_inner_smul_right,hee,mul_one] using
      (hasDerivAt_const s e).inner ℝ (hJ s)
  have hsol (s : ℝ) := constant_curvature_jacobi_solution (E := ℝ) convex_univ (mem_univ 0) κ
    (fun s _ => hq s) (fun s _ => by simpa only [smul_eq_mul] using ha s)
    (show q 0 = 0 by simp [q,J,F]) (show a 0 = 1 by simp [a,F]) (mem_univ s)
  have has (s : ℝ) : a s = curvatureCos κ s := by
    simpa only [smul_eq_mul,mul_one] using (hsol s).2
  have hdiff (s : ℝ) : HasDerivAt (fun s => J s - curvatureSin κ s • e) 0 s := by
    have hh := (hJ s).sub ((hasDerivAt_curvatureSin κ s).smul_const e)
    simpa only [has s,sub_self] using! hh
  have heq := eq_of_hasDerivAt_zero_on_convex convex_univ
    (fun s _ => hdiff s) (mem_univ 0) (mem_univ t)
  have hJs : J t = curvatureSin κ t • e := by
    simpa only [J,F,radialExponentialFlow_zero,curvatureSin_zero,zero_smul,sub_zero,
      sub_eq_zero] using heq
  exact Prod.ext (has t) hJs

theorem radialExponential_smul_unit (κ r : ℝ) {e : E} (he : ‖e‖ = 1) :
    radialExponential κ (r • e) = (curvatureCos κ r,curvatureSin κ r • e) := by
  have hs : radialGenerator κ (r • e) = r • radialGenerator κ e :=
    (radialGeneratorLinear κ).map_smul r e
  simpa only [radialExponential,hs,radialExponentialFlow] using radialExponentialFlow_unit κ r he

theorem radialExponential_formula (κ : ℝ) (x : E) :
    radialExponential κ x = (curvatureCos κ ‖x‖,(curvatureSin κ ‖x‖ / ‖x‖) • x) := by
  by_cases hx : x = 0
  · subst x
    simp
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let e : E := ‖x‖⁻¹ • x
  have he : ‖e‖ = 1 := by
    simp [e,norm_smul,hn.ne']
  have hxe : ‖x‖ • e = x := by simp [e,smul_smul,hn.ne']
  have hh := radialExponential_smul_unit κ ‖x‖ he
  rw [hxe] at hh
  simpa only [e,smul_smul,div_eq_mul_inv] using hh

end OAI.Geometry.Nikodym
