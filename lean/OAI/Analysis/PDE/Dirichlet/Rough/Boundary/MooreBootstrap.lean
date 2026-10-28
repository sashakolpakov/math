import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.MooreChart

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {m n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "V" => CoordinateSpace n 4

local instance mooreBootstrapFirstGroup (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedAddCommGroup (X →L[ℝ] Y) := inferInstance
local instance mooreBootstrapFirstSpace (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedSpace ℝ (X →L[ℝ] Y) := inferInstance
local instance mooreBootstrapSecondGroup (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] Y) := inferInstance
local instance mooreBootstrapSecondSpace (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] Y) := inferInstance

/-- The C²→C⁴ boundary bootstrap for the actual chart-transformed Moore
determinant. Normal ellipticity is derived from positivity and the invertible
chart differential; it is not an additional analytic assumption. -/
theorem exists_C4_halfball_moore_representative
    (Bg : E → V →L[ℝ] V →L[ℝ] ℝ) (J : E → V →L[ℝ] E)
    (T : E → V →L[ℝ] V →L[ℝ] E) (load : E → ℝ)
    (hBg : ContDiff ℝ 2 Bg) (hJ : ContDiff ℝ 2 J) (hT : ContDiff ℝ 2 T)
    (hl : ContDiff ℝ 2 load)
    (ℓ : E →L[ℝ] ℝ) (ν : E) (hν : ℓ ν = 1) {R : ℝ} (hR : 0 < R)
    {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (ht : ∀ v, ℓ v = 0 → ContDiffOn ℝ 2 (constantDirectional f v) ({x | 0 ≤ ℓ x} ∩ ball 0 R))
    (htt : ∀ v, ℓ v = 0 → ∀ w, ℓ w = 0 →
      ContDiffOn ℝ 2 (constantDirectional (constantDirectional f v) w)
        ({x | 0 ≤ ℓ x} ∩ ball 0 R))
    (honto : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R), Function.Surjective (J x))
    (hpos : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R),
      (OAI.LinearAlgebra.Moore.complexify (mooreChartMatrix (Bg x) (J x) (T x) (fderiv ℝ f x)
        (fderiv ℝ (fderiv ℝ f) x))).PosDef)
    (he : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R),
      OAI.LinearAlgebra.Moore.mooreDet n (mooreChartMatrix (Bg x) (J x) (T x) (fderiv ℝ f x)
        (fderiv ℝ (fderiv ℝ f) x)) = load x) :
    ∃ g : E → ℝ, ContDiff ℝ 4 g ∧
      EqOn g f ({x | 0 ≤ ℓ x} ∩ closedBall 0 (R/4)) := by
  have hF := contDiff_mooreChartResidual hBg hJ hT hl
  apply exists_C4_halfball_representative (mooreChartResidual Bg J T load) hF ℓ ν hν hR hf ht htt
  · intro x hx
    exact sub_eq_zero.mpr (he x hx)
  · intro x hx
    have hℓ : ℓ ≠ 0 := by
      intro hz
      simp [hz] at hν
    exact (mooreChartResidual_normal_pos (nonlinearTwoJet f x) ℓ hℓ (honto x hx)
      (hpos x hx) (hF.differentiable (by norm_num) _)).ne'

end OAI.Analysis.PDE.Dirichlet
