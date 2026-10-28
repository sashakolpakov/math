import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.MooreBootstrap

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {m n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "V" => CoordinateSpace n 4

local instance physicalBootstrapFirstGroup (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedAddCommGroup (X →L[ℝ] Y) := inferInstance
local instance physicalBootstrapFirstSpace (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedSpace ℝ (X →L[ℝ] Y) := inferInstance
local instance physicalBootstrapSecondGroup (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] Y) := inferInstance
local instance physicalBootstrapSecondSpace (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] Y) := inferInstance

theorem mooreChartMatrix_of_local_inverse
    {ψ : V → ℝ} {G : E → V} {P : V → E} {x : E}
    (hψ : ContDiffAt ℝ 2 ψ (G x)) (hG : ContDiffAt ℝ 2 G x)
    (hP : ContDiffAt ℝ 2 P (G x)) (hPG : P (G x) = x)
    (hGP : (fun y ↦ G (P y)) =ᶠ[𝓝 (G x)] id) :
    mooreChartMatrix 0 (fderiv ℝ P (G x)) (fderiv ℝ (fderiv ℝ P) (G x))
      (fderiv ℝ (ψ ∘ G) x) (fderiv ℝ (fderiv ℝ (ψ ∘ G)) x) =
        quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x) := by
  have hf : ContDiffAt ℝ 2 (ψ ∘ G) (P (G x)) := by
    rw [hPG]
    exact hψ.comp x hG
  have hmat := mooreChartMatrix_eq_quaternionHessian
    (u₀ := fun _ : V ↦ (0 : ℝ)) contDiffAt_const hf hP
  have hz : fderiv ℝ (fderiv ℝ (fun _ : V ↦ (0 : ℝ))) (G x) = 0 := by
    simp
  rw [hz,hPG] at hmat
  refine hmat.trans (quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots ?_)
  filter_upwards [hGP] with y hy
  change 0 + ψ (G (P y)) = ψ y
  simp only [zero_add,hy,id_eq]

/-- A C² positive solution of the actual physical Moore equation becomes
C⁴ up to the boundary once the first and second tangential C² jets supplied
by the parameterized inverse have been identified. The chart hypotheses are
the genuine local inverse identities, not a separately assumed ellipticity. -/
theorem exists_C4_moore_chart_representative
    {ψ : V → ℝ} (hψ : ContDiff ℝ 2 ψ) (G : E → V) (P : V → E)
    (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    (load : V → ℝ) (hl : ContDiff ℝ ∞ load)
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1) {R : ℝ} (hR : 0 < R)
    (hPG : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R), (fun y ↦ P (G y)) =ᶠ[𝓝 x] id)
    (hGP : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R), (fun y ↦ G (P y)) =ᶠ[𝓝 (G x)] id)
    (ht : ∀ v, ℓ v = 0 → ContDiffOn ℝ 2 (constantDirectional (ψ ∘ G) v)
      ({x | 0 ≤ ℓ x} ∩ ball 0 R))
    (htt : ∀ v, ℓ v = 0 → ∀ w, ℓ w = 0 →
      ContDiffOn ℝ 2 (constantDirectional (constantDirectional (ψ ∘ G) v) w)
        ({x | 0 ≤ ℓ x} ∩ ball 0 R))
    (hpos : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R),
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x))).PosDef)
    (he : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R),
      OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x)) = load (G x)) :
    ∃ g : E → ℝ, ContDiff ℝ 4 g ∧
      EqOn g (ψ ∘ G) ({x | 0 ≤ ℓ x} ∩ closedBall 0 (R/4)) := by
  let J : E → V →L[ℝ] E := fun x ↦ fderiv ℝ P (G x)
  let T : E → V →L[ℝ] V →L[ℝ] E := fun x ↦ fderiv ℝ (fderiv ℝ P) (G x)
  have hJ : ContDiff ℝ 2 J := (hP.fderiv_right (m := 2) (by simp)).comp (hG.of_le (by simp))
  have hT : ContDiff ℝ 2 T := ((hP.fderiv_right (m := ∞) (by simp)).fderiv_right
    (m := 2) (by simp)).comp (hG.of_le (by simp))
  have hm (x : E) (hx : x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R)) :
      mooreChartMatrix 0 (J x) (T x) (fderiv ℝ (ψ ∘ G) x)
        (fderiv ℝ (fderiv ℝ (ψ ∘ G)) x) = quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x) :=
    mooreChartMatrix_of_local_inverse hψ.contDiffAt (hG.contDiffAt.of_le (by simp))
      (hP.contDiffAt.of_le (by simp)) (hPG x hx).eq_of_nhds (hGP x hx)
  apply exists_C4_halfball_moore_representative (fun _ ↦ 0) J T (load ∘ G)
    contDiff_const hJ hT ((hl.of_le (by simp)).comp (hG.of_le (by simp)))
    ℓ ν hν hR (hψ.comp (hG.of_le (by simp))) ht htt
  · intro x hx
    exact fderiv_left_inverse_surjective (hG.differentiable (by simp) x)
      (hP.differentiable (by simp) (G x)) (hPG x hx)
  · intro x hx
    rw [hm x hx]
    exact hpos x hx
  · intro x hx
    rw [hm x hx]
    exact he x hx

end OAI.Analysis.PDE.Dirichlet
