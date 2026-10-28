import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.MoorePhysical
import OAI.Analysis.PDE.Dirichlet.Rough.FixedDomainSmooth
import OAI.Analysis.Calculus.SmoothExtension.HalfspaceExtension

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {m n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "V" => CoordinateSpace n 4

local instance smoothLocalFirstGroup (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedAddCommGroup (X →L[ℝ] Y) := inferInstance
local instance smoothLocalFirstSpace (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedSpace ℝ (X →L[ℝ] Y) := inferInstance
local instance smoothLocalSecondGroup (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] Y) := inferInstance
local instance smoothLocalSecondSpace (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] Y) := inferInstance

/-- The exact chart matrix when the unknown is the difference from a
smooth boundary background. Only C² regularity of the solution is used. -/
theorem mooreChartMatrix_background_of_local_inverse
    {ψ B : V → ℝ} {G : E → V} {P : V → E} {x : E}
    (hψ : ContDiffAt ℝ 2 ψ (G x)) (hB : ContDiffAt ℝ 2 B (G x))
    (hG : ContDiffAt ℝ 2 G x) (hP : ContDiffAt ℝ 2 P (G x))
    (hPG : P (G x) = x) (hGP : (fun y ↦ G (P y)) =ᶠ[𝓝 (G x)] id) :
    mooreChartMatrix (fderiv ℝ (fderiv ℝ B) (G x))
      (fderiv ℝ P (G x)) (fderiv ℝ (fderiv ℝ P) (G x))
      (fderiv ℝ (fun z ↦ ψ (G z) - B (G z)) x)
      (fderiv ℝ (fderiv ℝ (fun z ↦ ψ (G z) - B (G z))) x) =
      quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x) := by
  have hf : ContDiffAt ℝ 2 (fun z ↦ ψ (G z) - B (G z)) (P (G x)) := by
    rw [hPG]
    exact (hψ.comp x hG).sub (hB.comp x hG)
  have hm := mooreChartMatrix_eq_quaternionHessian hB hf hP
  rw [hPG] at hm
  refine hm.trans (quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots ?_)
  filter_upwards [hGP] with y hy
  simp only [hy,id_eq]
  ring

/-- All-order tangential jets and positivity of the actual Moore matrix
give smoothness on one fixed closed half-patch. -/
theorem contDiffOn_infty_moore_halfpatch
    (Bg : E → V →L[ℝ] V →L[ℝ] ℝ) (J : E → V →L[ℝ] E)
    (T : E → V →L[ℝ] V →L[ℝ] E) (load : E → ℝ)
    (hBg : ContDiff ℝ ∞ Bg) (hJ : ContDiff ℝ ∞ J)
    (hT : ContDiff ℝ ∞ T) (hl : ContDiff ℝ ∞ load)
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    {O : Set E} (hO : IsOpen O) {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hi : ∀ x ∈ O, 0 < ℓ x → ContDiffAt ℝ ∞ f x)
    (ht : ∀ (N : ℕ) (v : Fin N → ℓ.ker), ContDiffOn ℝ 2
      (fun z ↦ iteratedFDeriv ℝ N (fun t : ℓ.ker ↦ f (z+(t:E))) 0 v)
      ({x | 0 ≤ ℓ x} ∩ O))
    (honto : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ O), Function.Surjective (J x))
    (hpos : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ O),
      (OAI.LinearAlgebra.Moore.complexify (mooreChartMatrix (Bg x) (J x) (T x) (fderiv ℝ f x)
        (fderiv ℝ (fderiv ℝ f) x))).PosDef)
    (he : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ O),
      OAI.LinearAlgebra.Moore.mooreDet n (mooreChartMatrix (Bg x) (J x) (T x) (fderiv ℝ f x)
        (fderiv ℝ (fderiv ℝ f) x)) = load x) :
    ContDiffOn ℝ ∞ f ({x | 0 ≤ ℓ x} ∩ O) := by
  have hF := contDiff_mooreChartResidual hBg hJ hT hl
  apply contDiffOn_infty_halfspace_of_mixed_tangents
    (mooreChartResidual Bg J T load) hF ℓ ν hν hO hf hi ht
  · intro x hx
    exact sub_eq_zero.mpr (he x hx)
  · intro x hx
    have hℓ : ℓ ≠ 0 := by
      intro hz
      simp [hz] at hν
    exact (mooreChartResidual_normal_pos (nonlinearTwoJet f x) ℓ hℓ (honto x hx)
      (hpos x hx) (hF.differentiable (by simp) _)).ne'

/-- Smoothness up to a genuine Moore boundary chart, without assuming
any derivatives of the solution beyond C² in advance. -/
theorem contDiffOn_infty_moore_chart
    {ψ B : V → ℝ} (hψ : ContDiff ℝ 2 ψ) (hB : ContDiff ℝ ∞ B)
    (G : E → V) (P : V → E) (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    (load : V → ℝ) (hl : ContDiff ℝ ∞ load)
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1)
    {O : Set E} (hO : IsOpen O)
    (hPG : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ O), (fun y ↦ P (G y)) =ᶠ[𝓝 x] id)
    (hGP : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ O), (fun y ↦ G (P y)) =ᶠ[𝓝 (G x)] id)
    (hi : ∀ x ∈ O, 0 < ℓ x → ContDiffAt ℝ ∞ ψ (G x))
    (ht : ∀ (N : ℕ) (v : Fin N → ℓ.ker), ContDiffOn ℝ 2
      (fun z ↦ iteratedFDeriv ℝ N
        (fun t : ℓ.ker ↦ ψ (G (z+(t:E))) - B (G (z+(t:E)))) 0 v)
      ({x | 0 ≤ ℓ x} ∩ O))
    (hpos : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ O),
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x))).PosDef)
    (he : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ O),
      OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x)) = load (G x)) :
    ContDiffOn ℝ ∞ (ψ ∘ G) ({x | 0 ≤ ℓ x} ∩ O) := by
  let f : E → ℝ := fun z ↦ ψ (G z) - B (G z)
  let Bg : E → V →L[ℝ] V →L[ℝ] ℝ := fun x ↦ fderiv ℝ (fderiv ℝ B) (G x)
  let J : E → V →L[ℝ] E := fun x ↦ fderiv ℝ P (G x)
  let T : E → V →L[ℝ] V →L[ℝ] E := fun x ↦ fderiv ℝ (fderiv ℝ P) (G x)
  have hBg : ContDiff ℝ ∞ Bg :=
    ((hB.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).comp hG
  have hJ : ContDiff ℝ ∞ J := (hP.fderiv_right (m := ∞) (by simp)).comp hG
  have hT : ContDiff ℝ ∞ T :=
    ((hP.fderiv_right (m := ∞) (by simp)).fderiv_right (m := ∞) (by simp)).comp hG
  have hm (x : E) (hx : x ∈ ({x | 0 ≤ ℓ x} ∩ O)) :
      mooreChartMatrix (Bg x) (J x) (T x) (fderiv ℝ f x)
        (fderiv ℝ (fderiv ℝ f) x) = quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x) :=
    mooreChartMatrix_background_of_local_inverse hψ.contDiffAt
      (hB.contDiffAt.of_le (by simp)) (hG.contDiffAt.of_le (by simp))
      (hP.contDiffAt.of_le (by simp)) (hPG x hx).eq_of_nhds (hGP x hx)
  have hf : ContDiff ℝ 2 f :=
    (hψ.comp (hG.of_le (by simp))).sub ((hB.comp hG).of_le (by simp))
  have hs : ContDiffOn ℝ ∞ f ({x | 0 ≤ ℓ x} ∩ O) := by
    apply contDiffOn_infty_moore_halfpatch Bg J T (load ∘ G) hBg hJ hT (hl.comp hG)
      ℓ ν hν hO hf
    · intro x hx hp
      exact ((hi x hx hp).comp x hG.contDiffAt).sub (hB.comp hG).contDiffAt
    · exact ht
    · intro x hx
      exact fderiv_left_inverse_surjective (hG.differentiable (by simp) x)
        (hP.differentiable (by simp) (G x)) (hPG x hx)
    · intro x hx
      rw [hm x hx]
      exact hpos x hx
    · intro x hx
      rw [hm x hx]
      exact he x hx
  have heq : (ψ ∘ G) = fun z ↦ f z + B (G z) := by
    funext z
    simp [f]
  rw [heq]
  exact hs.add (hB.comp hG).contDiffOn

end OAI.Analysis.PDE.Dirichlet
