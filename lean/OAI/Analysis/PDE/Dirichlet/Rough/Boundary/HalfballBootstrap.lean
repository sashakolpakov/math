import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.FourthBootstrap
import OAI.Analysis.Calculus.FiniteExtension.Halfspace.Extension.Ball

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

theorem eqOn_fderiv_of_uniqueDiff {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set E} (hS : UniqueDiffOn ℝ S) {f g : E → F} (he : EqOn g f S)
    (hf : ∀ x ∈ S, DifferentiableAt ℝ f x) (hg : ∀ x ∈ S, DifferentiableAt ℝ g x) :
    EqOn (fderiv ℝ g) (fderiv ℝ f) S := by
  intro x hx
  rw [← fderivWithin_eq_fderiv (hS x hx) (hg x hx),
    fderivWithin_congr' he hx, fderivWithin_eq_fderiv (hS x hx) (hf x hx)]

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local instance halfballBootstrapFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance halfballBootstrapFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance halfballBootstrapSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance halfballBootstrapSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The full local C²→C⁴ bootstrap, with genuine reflected representatives.
The hypotheses require only the C² tangential jets extracted from a smooth
Banach curve, not a C³ or C⁴ representative of the original solution. -/
theorem exists_C4_halfball_representative
    (F : NonlinearJet E → ℝ) (hF : ContDiff ℝ 2 F)
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1) {R : ℝ} (hR : 0 < R)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (ht : ∀ v, ℓ v = 0 → ContDiffOn ℝ 2 (constantDirectional f v) ({x | 0 ≤ ℓ x} ∩ ball 0 R))
    (htt : ∀ v, ℓ v = 0 → ∀ w, ℓ w = 0 →
      ContDiffOn ℝ 2 (constantDirectional (constantDirectional f v) w)
        ({x | 0 ≤ ℓ x} ∩ ball 0 R))
    (he : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R), F (nonlinearTwoJet f x) = 0)
    (hell : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R),
      fderiv ℝ F (nonlinearTwoJet f x) (0,ℓ.smulRight ℓ) ≠ 0) :
    ∃ g : E → ℝ, ContDiff ℝ 4 g ∧
      EqOn g f ({x | 0 ≤ ℓ x} ∩ closedBall 0 (R/4)) := by
  let S : Set E := {x | 0 ≤ ℓ x} ∩ ball 0 R
  have hS : UniqueDiffOn ℝ S :=
    (OAI.Analysis.Calculus.FiniteExtension.uniqueDiffOn_positive_halfspace ℓ ν hν).inter isOpen_ball
  have hf3 : ContDiffOn ℝ 3 f S :=
    contDiffOn_of_nonlinear_equation_and_tangents F ℓ ν hν hS (k := 1) (by norm_num)
      hf.contDiffOn (fun x _ ↦ hf.contDiffAt) ht
      (fun x _ ↦ (hF.of_le (by norm_num)).contDiffAt) he hell
  obtain ⟨g,hg,hgf⟩ := OAI.Analysis.Calculus.FiniteExtension.exists_contDiff_extension_halfball ℓ ν hν hR f hf3
  let T : Set E := {x | 0 ≤ ℓ x} ∩ ball 0 (R/2)
  have hT : UniqueDiffOn ℝ T :=
    (OAI.Analysis.Calculus.FiniteExtension.uniqueDiffOn_positive_halfspace ℓ ν hν).inter isOpen_ball
  have hTS : T ⊆ S := fun x hx ↦ ⟨hx.1, ball_subset_ball (by linarith) hx.2⟩
  have he0 : EqOn g f T := fun x hx ↦ hgf ⟨hx.1,ball_subset_closedBall hx.2⟩
  have he1 : EqOn (fderiv ℝ g) (fderiv ℝ f) T := eqOn_fderiv_of_uniqueDiff hT he0
    (fun x _ ↦ hf.differentiable (by norm_num) x)
    (fun x _ ↦ hg.differentiable (by norm_num) x)
  have he2 : EqOn (fderiv ℝ (fderiv ℝ g)) (fderiv ℝ (fderiv ℝ f)) T :=
    eqOn_fderiv_of_uniqueDiff hT he1
      (fun x _ ↦ (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
      (fun x _ ↦ (hg.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num) x)
  have hjet (x : E) (hx : x ∈ T) : nonlinearTwoJet g x = nonlinearTwoJet f x := by
    simp only [nonlinearTwoJet,he1 hx,he2 hx]
  have ht2 (v : E) (hv : ℓ v = 0) (w : E) (hw : ℓ w = 0) :
      ContDiffOn ℝ 2 (constantDirectional (constantDirectional g v) w) T := by
    apply ((htt v hv w hw).mono hTS).congr
    intro x hx
    change fderiv ℝ (constantDirectional g v) x w = fderiv ℝ (constantDirectional f v) x w
    rw [fderiv_constantDirectional_apply (hg.contDiffAt.of_le (by norm_num)),
      fderiv_constantDirectional_apply hf.contDiffAt,he2 hx]
  have hg4 : ContDiffOn ℝ 4 g T := contDiffOn_four_of_second_tangents F hF ℓ ν hν hT hg ht2
    (fun x hx ↦ by rw [hjet x hx]; exact he x (hTS hx))
    (fun x hx ↦ by rw [hjet x hx]; exact hell x (hTS hx))
  obtain ⟨u,hu,hug⟩ := OAI.Analysis.Calculus.FiniteExtension.exists_contDiff_extension_halfball ℓ ν hν
    (half_pos hR) g hg4
  refine ⟨u,hu,?_⟩
  intro x hx
  have hhalf : R/2/2 = R/4 := by ring
  rw [hug ⟨hx.1,by simpa only [hhalf] using hx.2⟩]
  exact hgf ⟨hx.1,closedBall_subset_closedBall (by linarith) hx.2⟩

end OAI.Analysis.PDE.Dirichlet
