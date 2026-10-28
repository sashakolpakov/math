import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Normalization
import OAI.Analysis.Fourier.Dispersion.Propagator

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.Dispersion

/-- Positive quadratic dispersion is a genuine invertible linear transform
of radial dispersion; the factor is constructed from the positive square root. -/
theorem exists_quadratic_dispersion_factor {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) :
    ∃ R : Space n ≃L[ℝ] Space n, ∀ ξ : Space n,
      inner ℝ ξ (Matrix.toEuclideanCLM (𝕜 := ℝ) Q ξ) = ‖R ξ‖^2 := by
  obtain ⟨R,-,hR⟩ := OAI.Analysis.PDE.Schauder.exists_elliptic_normalization Q hQ
  exact ⟨R,fun ξ => (hR ξ).symm⟩

def quadraticDispersion {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (m : ℝ)
    (ξ : Space n) : ℝ :=
  Real.sqrt (m^2 + inner ℝ ξ (Matrix.toEuclideanCLM (𝕜 := ℝ) Q ξ))

theorem quadraticDispersion_continuous {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (m : ℝ) : Continuous (quadraticDispersion Q m) := by
  unfold quadraticDispersion
  fun_prop

theorem quadraticDispersion_eq_radial_comp {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) :
    ∃ R : Space n ≃L[ℝ] Space n, ∀ m : ℝ,
      quadraticDispersion Q m = (fun ξ : Space n => Real.sqrt (m^2+‖ξ‖^2)) ∘ R := by
  obtain ⟨R,hR⟩ := exists_quadratic_dispersion_factor Q hQ
  exact ⟨R,fun m => funext fun ξ => by simp [quadraticDispersion,hR]⟩

end OAI.Analysis.Fourier.Dispersion
