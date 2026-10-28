import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.Implicit

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Smooth dependence of actual global inverses follows from parametric
IFT and injectivity. No continuity assumption is made on `invFun`. -/
theorem contDiffAt_parametric_invFun
    (F : P × E → E) {a : P} {y : E} {q : ℕ∞ω} (hq : q ≠ 0)
    (hbij : ∀ᶠ t in 𝓝 a, Function.Bijective (fun x ↦ F (t, x)))
    (hF : ContDiffAt ℝ q F (a, Function.invFun (fun x ↦ F (a, x)) y))
    (hD : (fderiv ℝ (fun x ↦ F (a, x))
      (Function.invFun (fun x ↦ F (a, x)) y)).IsInvertible) :
    ContDiffAt ℝ q (fun ty : P × E ↦ Function.invFun (fun x ↦ F (ty.1, x)) ty.2) (a, y) := by
  let x := Function.invFun (fun x ↦ F (a, x)) y
  have hx : F (a, x) = y := Function.invFun_eq ((hbij.self_of_nhds).surjective y)
  let Q : (P × E) × E → E := fun p ↦ F (p.1.1, p.2) - p.1.2
  have hQ : ContDiffAt ℝ q Q ((a, y), x) :=
    (hF.comp ((a, y), x) (contDiffAt_fst.fst.prodMk contDiffAt_snd)).sub contDiffAt_fst.snd
  have hdQ : DifferentiableAt ℝ Q ((a, y), x) := hQ.differentiableAt hq
  have hslice : DifferentiableAt ℝ (fun z ↦ F (a, z)) x :=
    (hF.comp x (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt hq
  have hpart : ((fderiv ℝ Q ((a, y), x)).comp
      (ContinuousLinearMap.inr ℝ (P × E) E)) = fderiv ℝ (fun z ↦ F (a, z)) x := by
    have hi : HasFDerivAt (fun z : E ↦ ((a, y), z))
        (ContinuousLinearMap.inr ℝ (P × E) E) x := by
      change HasFDerivAt (fun z : E ↦ ((a, y), z))
        ((0 : E →L[ℝ] P × E).prod (ContinuousLinearMap.id ℝ E)) x
      simpa only [id_eq] using
        (hasFDerivAt_const (a, y) x).prodMk (hasFDerivAt_id x)
    exact ((hdQ.hasFDerivAt.comp x hi).fderiv).symm.trans (hslice.hasFDerivAt.sub_const y).fderiv
  apply contDiffAt_of_implicit_global_uniqueness Q hQ hq (hpart ▸ hD) _
    (S := univ) univ_mem
  have ht : ∀ᶠ p : P × E in 𝓝 (a, y), Function.Bijective (fun z ↦ F (p.1, z)) :=
    (continuous_fst.tendsto (a, y)).eventually hbij
  filter_upwards [ht] with p hp z hz heq
  have he : F (p.1, z) = p.2 := by
    change F (p.1, z) - p.2 = F (a, x) - y at heq
    rw [hx, sub_self] at heq
    exact sub_eq_zero.mp heq
  exact hp.injective (he.trans (Function.invFun_eq (hp.surjective p.2)).symm)

end OAI.Analysis.PDE.Dirichlet
