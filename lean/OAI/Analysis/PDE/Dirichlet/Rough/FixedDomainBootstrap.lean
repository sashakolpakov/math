import OAI.Analysis.PDE.Dirichlet.Rough.HigherLocalization
import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.HalfballBootstrap

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

local instance fixedBootstrapFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fixedBootstrapFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fixedBootstrapSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fixedBootstrapSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- One regularity step at an arbitrary boundary point. Finite extension
is used only locally; the conclusion remains on the original fixed domain. -/
theorem contDiffWithinAt_higher_at_boundary (k : ℕ)
    (F : NonlinearJet E → ℝ) (hF : ContDiff ℝ (k+1) F)
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    {O : Set E} (hO : IsOpen O) {a : E} (ha : a ∈ O) (hℓa : ℓ a = 0)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hh : ContDiffOn ℝ (k+2) f ({x | 0 ≤ ℓ x} ∩ O))
    (ht : ∀ v : Fin (k+1) → ℓ.ker, ContDiffOn ℝ 2
      (fun z ↦ iteratedFDeriv ℝ (k+1) (fun t : ℓ.ker ↦ f (z+(t:E))) 0 v)
      ({x | 0 ≤ ℓ x} ∩ O))
    (he : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ O), F (nonlinearTwoJet f x) = 0)
    (hell : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ O),
      fderiv ℝ F (nonlinearTwoJet f x) (0,ℓ.smulRight ℓ) ≠ 0) :
    ContDiffWithinAt ℝ (k+3) f ({x | 0 ≤ ℓ x} ∩ O) a := by
  obtain ⟨R,hR,hRO⟩ := Metric.isOpen_iff.mp hO a ha
  have hRS : {x | 0 ≤ ℓ x} ∩ ball a R ⊆ {x | 0 ≤ ℓ x} ∩ O :=
    fun x hx ↦ ⟨hx.1,hRO hx.2⟩
  obtain ⟨g,hg,hgf⟩ := exists_contDiff_extension_halfball_at ℓ ν hν hℓa hR f (hh.mono hRS)
  let T : Set E := {x | 0 ≤ ℓ x} ∩ ball a (R/2)
  have hTS : T ⊆ {x | 0 ≤ ℓ x} ∩ O := fun x hx ↦
    hRS ⟨hx.1,ball_subset_ball (by linarith) hx.2⟩
  have hT : UniqueDiffOn ℝ T :=
    (OAI.Analysis.Calculus.FiniteExtension.uniqueDiffOn_positive_halfspace ℓ ν hν).inter isOpen_ball
  have h0 : EqOn g f T := fun x hx ↦ hgf ⟨hx.1,ball_subset_closedBall hx.2⟩
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by exact_mod_cast (by omega : 2 ≤ k+2))
  have h1 : EqOn (fderiv ℝ g) (fderiv ℝ f) T := eqOn_fderiv_of_uniqueDiff hT h0
    (fun x _ ↦ hf.differentiable (by norm_num) x)
    (fun x _ ↦ hg2.differentiable (by norm_num) x)
  have h2 : EqOn (fderiv ℝ (fderiv ℝ g)) (fderiv ℝ (fderiv ℝ f)) T :=
    eqOn_fderiv_of_uniqueDiff hT h1
      (fun x _ ↦ (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
      (fun x _ ↦ (hg2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
  have hjet (x : E) (hx : x ∈ T) : nonlinearTwoJet g x = nonlinearTwoJet f x := by
    simp only [nonlinearTwoJet,h1 hx,h2 hx]
  have htensor (v : Fin (k+1) → ℓ.ker) : ContDiffOn ℝ 2
      (fun z ↦ iteratedFDeriv ℝ (k+1) (fun t : ℓ.ker ↦ g (z+(t:E))) 0 v) T := by
    apply ((ht v).mono hTS).congr
    intro z hz
    exact tangent_parameter_tensors_congr ℓ h0 hz (k+1) v
  have hgup : ContDiffOn ℝ (k+3) g T := by
    apply contDiffOn_higher_of_iterated_tangents k F hF ℓ ν hν hT hg
    · intro vs hlen hvs
      apply contDiffOn_iterated_tangent_of_parameter_tensors ℓ vs
        (hg.of_le (by rw [hlen]; exact_mod_cast (by omega : k+1 ≤ k+2))) hvs
      intro v
      have hall : ∀ (N : ℕ), N = k+1 → ∀ w : Fin N → ℓ.ker,
          ContDiffOn ℝ 2 (fun z ↦ iteratedFDeriv ℝ N
            (fun t : ℓ.ker ↦ g (z+(t:E))) 0 w) T := by
        intro N hN
        subst N
        exact htensor
      exact hall vs.length hlen v
    · exact fun x hx ↦ by rw [hjet x hx]; exact he x (hTS hx)
    · exact fun x hx ↦ by rw [hjet x hx]; exact hell x (hTS hx)
  have haT : a ∈ T := ⟨by simp only [Set.mem_ofPred_eq,hℓa,le_refl],mem_ball_self (half_pos hR)⟩
  have hfup : ContDiffWithinAt ℝ (k+3) f T a :=
    (hgup a haT).congr (fun x hx ↦ (h0 hx).symm) (h0 haT).symm
  apply hfup.mono_of_mem_nhdsWithin
  have hhalf : {x | 0 ≤ ℓ x} ∈ 𝓝[{x | 0 ≤ ℓ x} ∩ O] a :=
    Filter.mem_of_superset self_mem_nhdsWithin inter_subset_left
  exact Filter.inter_mem hhalf (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds a (half_pos hR)))

end OAI.Analysis.PDE.Dirichlet
