import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension.Sum

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.PDE.Variational

variable {E T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [AddCommGroup T]

/-- Smooth weighted periodization with a harmless smooth reciprocal away
from the closed domain. No positivity is required outside that domain. -/
theorem exists_periodic_extension_of_weight
    (L : T →+ E) (hL : ∀R : ℝ, {z : T | ‖L z‖ ≤ R}.Finite)
    {q : ℕ} {K : Set E} (hK : ∀x ∈ K, ∀z, x + L z ∈ K)
    (u g ρ : E → ℝ) (hu : ∀x ∈ K, ∀z, u (x + L z) = u x)
    (hg : ContDiff ℝ q g) (hgu : ∀x ∈ K, g x = u x)
    (hρ : ContDiff ℝ q ρ) (hρc : HasCompactSupport ρ)
    (hρ0 : ∀x, 0 ≤ ρ x) (hρ1 : ∀x ∈ K, ∃z, ρ (x + L z) = 1) :
    ∃f : E → ℝ, ContDiff ℝ q f ∧
      (∀x z, f (x + L z) = f x) ∧ ∀x ∈ K, f x = u x := by
  let D := OAI.Analysis.PDE.Variational.discretePeriodization L ρ
  let B := OAI.Analysis.PDE.Variational.discretePeriodization L (fun x ↦ ρ x * g x)
  have hDc : ContDiff ℝ q D := contDiff_discretePeriodization_order L hL hρ hρc
  have hBc : ContDiff ℝ q B :=
    contDiff_discretePeriodization_order L hL (hρ.mul hg) hρc.mul_right
  refine ⟨fun x ↦ smoothReciprocal (D x) * B x,
    ((contDiff_smoothReciprocal.of_le (by simp)).comp hDc).mul hBc, ?_, ?_⟩
  · intro x z
    simp only [D,B,OAI.Analysis.PDE.Variational.discretePeriodization_add]
  · intro x hx
    have hD1 : 1 ≤ D x := by
      obtain ⟨z,hz⟩ := hρ1 x hx
      rw [← hz]
      exact (summable_discrete_translates L hL hρc x).le_tsum z (fun j _ ↦ hρ0 _)
    have hB : B x = D x * u x := by
      calc
        B x = ∑'z, ρ (x + L z) * u x := by
          apply tsum_congr
          intro z
          change ρ (x + L z) * g (x + L z) = _
          rw [hgu _ (hK x hx z),hu x hx z]
        _ = D x * u x := by rw [tsum_mul_right]; rfl
    change smoothReciprocal (D x) * B x = u x
    rw [hB,← mul_assoc,smoothReciprocal_mul hD1,one_mul]

end OAI.Analysis.Calculus.SmoothExtension
