import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Jets
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Glue
import OAI.Analysis.PDE.Dirichlet.CoordinateTransport

/-! Odd reflection is genuinely C² when the zero trace and normal second jet match. -/

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem second_fderiv_neg_pullback (u : E → ℝ) (hu : ContDiff ℝ 2 u)
    (L : E →L[ℝ] E) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => -u (L y))) x v w =
      -fderiv ℝ (fderiv ℝ u) (L x) (L v) (L w) := by
  have hfun : fderiv ℝ (fun y => -u (L y)) = fun y => -fderiv ℝ (u ∘ L) y := by
    funext y
    exact fderiv_neg
  rw [hfun]
  change fderiv ℝ (-(fderiv ℝ (u ∘ L))) x v w = _
  rw [fderiv_neg]
  change -(fderiv ℝ (fderiv ℝ (u ∘ L)) x v w) = _
  rw [OAI.Analysis.PDE.Dirichlet.second_fderiv_comp_between u hu L x v w]

theorem oddNormalExtension_jet_matching (e : E) (he : ‖e‖ = 1)
    (u : E → ℝ) (hu : ContDiff ℝ 2 u)
    (hzero : ∀ x, inner ℝ e x = 0 → u x = 0)
    (hnormal : ∀ x, inner ℝ e x = 0 → fderiv ℝ (fderiv ℝ u) x e e = 0) :
    (∀ x, inner ℝ e x = 0 → u x = -u (normalReflection e x)) ∧
    (∀ x, inner ℝ e x = 0 → fderiv ℝ u x = fderiv ℝ (fun y => -u (normalReflection e y)) x) ∧
    (∀ x, inner ℝ e x = 0 → fderiv ℝ (fderiv ℝ u) x =
      fderiv ℝ (fderiv ℝ (fun y => -u (normalReflection e y))) x) := by
  let R := normalReflection e
  let g := fun x => -u (R x)
  have hg : ContDiff ℝ 2 g := (hu.comp R.contDiff).neg
  have hd (x) : fderiv ℝ g x = -(fderiv ℝ u (R x)).comp R.toContinuousLinearEquiv.toContinuousLinearMap := by
    exact (((hu.differentiable (by norm_num) (R x)).hasFDerivAt.comp x
      R.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).neg).fderiv
  have hv (x) (hx : inner ℝ e x = 0) : u x = g x := by
    dsimp only [g, R]
    rw [normalReflection_eq_self e x he hx, hzero x hx]
    simp
  have hfirst (x) (hx : inner ℝ e x = 0) : fderiv ℝ u x = fderiv ℝ g x := by
    rw [hd]
    ext v
    change fderiv ℝ u x v = -fderiv ℝ u (R x) (R v)
    rw [show R x = x from normalReflection_eq_self e x he hx]
    rw [boundary_first_reflection u (hu.differentiable (by norm_num)) e x he hx hzero v, neg_neg]
  have hsecond (x) (hx : inner ℝ e x = 0) :
      fderiv ℝ (fderiv ℝ u) x = fderiv ℝ (fderiv ℝ g) x := by
    ext v w
    have ht := second_fderiv_neg_pullback u hu R.toContinuousLinearEquiv.toContinuousLinearMap x v w
    change fderiv ℝ (fderiv ℝ g) x v w = _ at ht
    rw [ht]
    change fderiv ℝ (fderiv ℝ u) x v w = -fderiv ℝ (fderiv ℝ u) (R x) (R v) (R w)
    rw [show R x = x from normalReflection_eq_self e x he hx]
    rw [boundary_bilinear_reflection e he _
      (fun a b ha hb => flat_boundary_hessian_zero u hu e x a b he hx ha hb hzero)
      (hnormal x hx) v w, neg_neg]
  exact ⟨hv, hfirst, hsecond⟩

theorem contDiff_oddNormalExtension (e : E) (he : ‖e‖ = 1)
    (u : E → ℝ) (hu : ContDiff ℝ 2 u)
    (hzero : ∀ x, inner ℝ e x = 0 → u x = 0)
    (hnormal : ∀ x, inner ℝ e x = 0 → fderiv ℝ (fderiv ℝ u) x e e = 0) :
    ContDiff ℝ 2 (oddNormalExtension e u) := by
  obtain ⟨hv, hfirst, hsecond⟩ := oddNormalExtension_jet_matching e he u hu hzero hnormal
  exact contDiff_two_levelGlue (fun x => inner ℝ e x) (innerSL ℝ e).continuous u
    (fun x => -u (normalReflection e x)) hu (hu.comp (normalReflection e).contDiff).neg hv hfirst hsecond

theorem second_fderiv_oddNormalExtension (e : E) (he : ‖e‖ = 1)
    (u : E → ℝ) (hu : ContDiff ℝ 2 u)
    (hzero : ∀ x, inner ℝ e x = 0 → u x = 0)
    (hnormal : ∀ x, inner ℝ e x = 0 → fderiv ℝ (fderiv ℝ u) x e e = 0)
    (x v w : E) :
    fderiv ℝ (fderiv ℝ (oddNormalExtension e u)) x v w =
      if 0 ≤ inner ℝ e x then fderiv ℝ (fderiv ℝ u) x v w
      else -fderiv ℝ (fderiv ℝ u) (normalReflection e x) (normalReflection e v) (normalReflection e w) := by
  obtain ⟨hv, hfirst, hsecond⟩ := oddNormalExtension_jet_matching e he u hu hzero hnormal
  have hh := second_fderiv_levelGlue (fun x => inner ℝ e x) (innerSL ℝ e).continuous u
    (fun x => -u (normalReflection e x)) hu (hu.comp (normalReflection e).contDiff).neg hv hfirst hsecond x
  change fderiv ℝ (fderiv ℝ (oddNormalExtension e u)) x = _ at hh
  rw [hh]
  by_cases hx : 0 ≤ inner ℝ e x
  · simp [levelGlue, hx]
  · simp only [levelGlue, ite_eq_right hx]
    exact second_fderiv_neg_pullback u hu (normalReflection e).toContinuousLinearEquiv.toContinuousLinearMap x v w

end OAI.Analysis.PDE.Schauder
