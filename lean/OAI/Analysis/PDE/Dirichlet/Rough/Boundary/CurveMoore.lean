import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.CurveTangents

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

variable {m n : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin m)
local notation "Y" => CoordinateSpace n 4

local instance curveMooreFirstGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance curveMooreFirstSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance curveMooreSecondGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance curveMooreSecondSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The exact parameter-curve identity is sufficient for C⁴ boundary
regularity of the actual Moore solution. The curves represent the unknown
minus the smooth prescribed boundary data, as in the transformed IFT. -/
theorem exists_C4_moore_chart_of_parameter_curves
    [Nontrivial Y] {r : Y → ℝ} {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (hr : ContDiff ℝ 3 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {ψ B₀ : Y → ℝ} (hψ : ContDiff ℝ 2 ψ) (hB₀ : ContDiff ℝ ∞ B₀)
    (G : X → Y) (P : Y → X) (hG : ContDiff ℝ ∞ G) (hP : ContDiff ℝ ∞ P)
    (load : Y → ℝ) (hl : ContDiff ℝ ∞ load)
    (ℓ : X →L[ℝ] ℝ) (ν : X) (hν : ℓ ν = 1) {R : ℝ} (hR : 0 < R)
    (hGS : MapsTo G ({x | 0 ≤ ℓ x} ∩ ball 0 R) {x | r x ≤ 0})
    (hPG : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R), (fun y ↦ P (G y)) =ᶠ[𝓝 x] id)
    (hGP : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R), (fun y ↦ G (P y)) =ᶠ[𝓝 (G x)] id)
    (hcurves : ∀ v, ℓ v = 0 → ∃ O : Set X, IsOpen O ∧ (0 : X) ∈ O ∧
      ∃ U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ContDiffAt ℝ 2 U 0 ∧
        ∀ z (hz : z ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R) ∩ O),
          (fun t ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) ⟨G z,hGS hz.1⟩) =ᶠ[𝓝 0]
            fun t ↦ ψ (G (z + t • v)) - B₀ (G (z + t • v)))
    (hpos : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R),
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x))).PosDef)
    (he : ∀ x ∈ ({x | 0 ≤ ℓ x} ∩ ball 0 R),
      OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ (G x)) = load (G x)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∃ g : X → ℝ, ContDiff ℝ 4 g ∧
      EqOn g (ψ ∘ G) ({x | 0 ≤ ℓ x} ∩ closedBall 0 ρ) := by
  let f : X → ℝ := fun x ↦ ψ (G x) - B₀ (G x)
  let b : X → ℝ := B₀ ∘ G
  have hf : ContDiff ℝ 2 f := (hψ.sub (hB₀.of_le (by simp))).comp (hG.of_le (by simp))
  have hb : ContDiff ℝ 4 b := (hB₀.of_le (by simp)).comp (hG.of_le (by simp))
  have hsum : (fun x ↦ f x + b x) = ψ ∘ G := by
    funext x
    dsimp [f,b]
    ring
  have hlocal := local_tangents_of_parameter_curves hr hreg
    (hG.of_le (by simp)).contDiffOn hGS (fun _ _ ↦ hf.contDiffAt) ℓ hcurves
  apply exists_C4_moore_chart_of_local_tangents hψ G P hG hP load hl ℓ ν hν hR hPG hGP
    _ hpos he
  intro v hv
  obtain ⟨O,hO,hzero,ht,htt⟩ := hlocal v hv
  refine ⟨O,hO,hzero,?_⟩
  have hadd := tangent_regularities_add_smooth (fun _ _ ↦ hf.contDiffAt) hb v ht htt
  simpa only [hsum] using hadd

end OAI.Analysis.PDE.Dirichlet
