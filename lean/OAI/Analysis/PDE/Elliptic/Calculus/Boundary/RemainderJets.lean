import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.LowerJets

noncomputable section
open Set
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
local instance remainderJetsFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance remainderJetsFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance remainderJetsSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance remainderJetsSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem norm_remainder_difference_le {F : Type*} [SeminormedAddCommGroup F] (a b c d : F) :
    ‖(a-b)-(c-d)‖ ≤ ‖a-c‖+‖b-d‖ := by
  rw [show (a-b)-(c-d) = (a-c)-(b-d) by abel]
  exact norm_sub_le _ _

omit [FiniteDimensional ℝ E] in
theorem c2JetHolderBoundsOn_sub {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    {S : Set E} {α A B : ℝ} (hfb : OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn f S α A)
    (hgb : OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn g S α B) :
    OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn (fun x => f x-g x) S α (A+B) := by
  have hd x : fderiv ℝ (fun y => f y-g y) x = fderiv ℝ f x-fderiv ℝ g x :=
    fderiv_sub (hf.differentiable (by norm_num) _) (hg.differentiable (by norm_num) _)
  have hd₂ x := second_fderiv_sub_fun f g hf hg x
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro x hx
    exact (norm_sub_le _ _).trans (add_le_add (hfb.value x hx) (hgb.value x hx))
  · intro x hx
    rw [hd]
    exact (norm_sub_le _ _).trans (add_le_add (hfb.first x hx) (hgb.first x hx))
  · intro x hx
    rw [hd₂]
    exact (norm_sub_le _ _).trans (add_le_add (hfb.second x hx) (hgb.second x hx))
  · intro x hx y hy
    exact (norm_remainder_difference_le _ _ _ _).trans
      ((add_le_add (hfb.value_sub x hx y hy) (hgb.value_sub x hx y hy)).trans_eq (add_mul _ _ _).symm)
  · intro x hx y hy
    rw [hd,hd]
    exact (norm_remainder_difference_le _ _ _ _).trans
      ((add_le_add (hfb.first_sub x hx y hy) (hgb.first_sub x hx y hy)).trans_eq (add_mul _ _ _).symm)
  · intro x hx y hy
    rw [hd₂,hd₂]
    exact (norm_remainder_difference_le _ _ _ _).trans
      ((add_le_add (hfb.second_sub x hx y hy) (hgb.second_sub x hx y hy)).trans_eq (add_mul _ _ _).symm)

omit [FiniteDimensional ℝ E] in
theorem c2JetHolderBoundsOn_mono {f : E → ℝ} {S : Set E} {α A B : ℝ}
    (h : OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn f S α A) (hAB : A ≤ B) : OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn f S α B := by
  refine ⟨fun x hx => (h.value x hx).trans hAB,
    fun x hx => (h.first x hx).trans hAB, fun x hx => (h.second x hx).trans hAB,?_,?_,?_⟩
  · intro x hx y hy
    exact (h.value_sub x hx y hy).trans (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (norm_nonneg _) _))
  · intro x hx y hy
    exact (h.first_sub x hx y hy).trans (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (norm_nonneg _) _))
  · intro x hx y hy
    exact (h.second_sub x hx y hy).trans (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (norm_nonneg _) _))

/-- All six lower-jet bounds of a fixed-chart boundary remainder, with
one uniform constant chosen before the solution and its stored jet. -/
theorem exists_chart_remainder_jet_bound
    (G : E → E) (hG : ContDiff ℝ 3 G) (B₀ : E → ℝ) (hB₀ : ContDiff ℝ 3 B₀)
    {S Ω K : Set E} (hS : IsCompact S) (hconv : Convex ℝ S)
    (hGK : MapsTo G S K) {hΩK : Ω ⊆ K}
    {α R : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hR : 0 ≤ R) :
    ∃ V > 0, ∀ u : E → ℝ, ContDiff ℝ 2 u →
      ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α, ‖U‖ ≤ R →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn ((fun x => u x-B₀ x) ∘ G) S α V := by
  obtain ⟨C,hC,hjet⟩ := OAI.Analysis.PDE.Dirichlet.exists_chart_jet_holder_bound G hG hS hconv hGK
    (hΩK := hΩK) hα hα1
  obtain ⟨B,hB,hbackground⟩ := OAI.Analysis.PDE.Dirichlet.exists_smooth_jet_holder_bounds (B₀ ∘ G) (hB₀.comp hG) hS hα hα1
  refine ⟨C*R+B,by positivity,?_⟩
  intro u hu U hUn hU0 hU1 hU2
  apply c2JetHolderBoundsOn_mono (c2JetHolderBoundsOn_sub
    (hu.comp (hG.of_le (by norm_num))) ((hB₀.comp hG).of_le (by norm_num))
    (hjet u hu U hU0 hU1 hU2) hbackground)
  exact add_le_add (mul_le_mul_of_nonneg_left hUn hC.le) le_rfl

end OAI.Analysis.PDE.Elliptic
