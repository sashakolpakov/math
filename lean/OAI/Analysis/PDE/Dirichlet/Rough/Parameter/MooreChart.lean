import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.Regularity
import OAI.Analysis.PDE.Dirichlet.Rough.Moore.SmoothLocal

noncomputable section
open Set Filter Metric Module
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {m n : ℕ} {P V ι : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
local notation "X" => EuclideanSpace ℝ (Fin m)
local notation "Y" => CoordinateSpace n 4

/-- Actual multi-parameter solution families give one genuinely smooth
boundary-chart representative, not a collection of finite-order extensions. -/
theorem HasGeometricSolutionFamilies.exists_smooth_chart_representative
    [Nontrivial Y] (j : X ≃ₗᵢ[ℝ] Y)
    {e : Y ≃L[ℝ] P × V} {b : Basis ι ℝ P} {r ψ B : Y → ℝ}
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (ℓ : X →L[ℝ] ℝ) (ν : X) (hν : ℓ ν = 1)
    (hc : ParameterDeformation.HasGeometricSolutionFamilies (Z := ℓ.ker) e b r ψ B hΩD α)
    (hi : ∀ x, r x < 0 → ContDiffAt ℝ ∞ ψ x)
    (hr : ContDiff ℝ 3 r) (hrp : LatticePeriodic e b r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (hψ : ContDiff ℝ 2 ψ) (hB : ContDiff ℝ ∞ B)
    (G : X → Y) (P' : Y → X) (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P')
    (load : Y → ℝ) (hl : ContDiff ℝ ∞ load)
    {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1)
    (hGS : MapsTo G ({x | 0 ≤ ℓ x} ∩ ball 0 R) {x | r x ≤ 0})
    (hPG : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R), (fun y ↦ P' (G y)) =ᶠ[𝓝 x] id)
    (hGP : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R), (fun y ↦ G (P' y)) =ᶠ[𝓝 (G x)] id)
    (c : ℝ) (hcpos : 0 < c)
    (hlevel : ∀ z ∈ ball (0 : X) 1, r (G z) = -c * ℓ z)
    (hpos : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R),
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x))).PosDef)
    (he : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R),
      OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x)) = load (G x)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∃ g : X → ℝ, ContDiff ℝ ∞ g ∧
      EqOn g (ψ ∘ G) ({x | 0 ≤ ℓ x} ∩ closedBall 0 ρ) := by
  have hzero : (0 : X) ∈ {x | 0 ≤ ℓ x} ∩ ball 0 R := by
    simp only [mem_inter_iff,Set.mem_ofPred_eq,map_zero,le_refl,true_and,mem_ball,dist_self]
    exact hR
  obtain ⟨O,hO,hzeroO,ht⟩ := hc.all_mixed_tangent_orders hr hrp hreg
    j G P' hG hP (hPG 0 hzero) ((-c) • ℓ) 0 (by
      intro z hz
      simpa only [zero_add,smul_apply,smul_eq_mul] using hlevel z hz)
    ℓ.ker.subtypeL (by
      intro t
      change (-c) * ℓ (t : X) = 0
      rw [show ℓ (t : X) = 0 from t.property,mul_zero]) hGS
  obtain ⟨ε,hε,hεO⟩ := Metric.isOpen_iff.mp hO 0 hzeroO
  let R₀ := min R ε
  have hR₀ : 0 < R₀ := lt_min hR hε
  have hsmall : {x | 0 ≤ ℓ x} ∩ ball 0 R₀ ⊆ {x | 0 ≤ ℓ x} ∩ ball 0 R :=
    fun x hx ↦ ⟨hx.1,ball_subset_ball (min_le_left _ _) hx.2⟩
  have hsmallO : {x | 0 ≤ ℓ x} ∩ ball 0 R₀ ⊆
      ({x | 0 ≤ ℓ x} ∩ ball 0 R) ∩ O :=
    fun x hx ↦ ⟨hsmall hx,hεO (ball_subset_ball (min_le_right _ _) hx.2)⟩
  have hs : ContDiffOn ℝ ∞ (ψ ∘ G) ({x | 0 ≤ ℓ x} ∩ ball 0 R₀) := by
    apply contDiffOn_infty_moore_chart hψ hB G P' hG hP load hl ℓ ν hν isOpen_ball
      (fun x hx ↦ hPG x (hsmall hx)) (fun x hx ↦ hGP x (hsmall hx))
    · intro x hx hp
      apply hi (G x)
      rw [hlevel x (ball_subset_ball ((min_le_left _ _).trans hR1) hx)]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hcpos) hp
    · intro N v
      exact (ht N v).mono hsmallO
    · exact fun x hx ↦ hpos x (hsmall hx)
    · exact fun x hx ↦ he x (hsmall hx)
  obtain ⟨g,hg,hgeq⟩ := OAI.Analysis.Calculus.SmoothExtension.exists_smooth_extension_of_halfball
    ℓ ν hν (ψ ∘ G) R₀ hR₀ (by simpa only [inter_comm] using hs)
  refine ⟨R₀/8,by positivity,?_,g,hg,?_⟩
  · have hle : R₀ ≤ R := min_le_left _ _
    linarith
  · intro x hx
    exact hgeq ⟨closedBall_subset_ball (by linarith : R₀/8 < R₀/4) hx.2,hx.1⟩

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
