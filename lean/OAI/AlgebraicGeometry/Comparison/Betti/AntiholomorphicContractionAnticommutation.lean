import OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContraction

/-! # Antiholomorphic Contraction Anticommutation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContractionAnticommutation.Dolbeault

noncomputable section

section

/-! The actual antiholomorphic contraction squares to zero. The proof
uses alternating covectors and polarization of ordinary contraction. -/

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covectorContraction_add_direction (n : ℕ) (v w : E)
    (a : E [⋀^Fin (n + 1)]→L[ℝ] ℂ) :
    AntiholomorphicContraction.Dolbeault.covectorContraction n (v + w) a = AntiholomorphicContraction.Dolbeault.covectorContraction n v a + AntiholomorphicContraction.Dolbeault.covectorContraction n w a :=
  a.curryLeft.map_add v w

theorem covectorContraction_same (n : ℕ) (v : E)
    (a : E [⋀^Fin (n + 2)]→L[ℝ] ℂ) :
    AntiholomorphicContraction.Dolbeault.covectorContraction n v (AntiholomorphicContraction.Dolbeault.covectorContraction (n + 1) v a) = 0 :=
  ContinuousAlternatingMap.curryLeft_same a v

theorem covectorContraction_anticommute (n : ℕ) (v w : E)
    (a : E [⋀^Fin (n + 2)]→L[ℝ] ℂ) :
    AntiholomorphicContraction.Dolbeault.covectorContraction n v (AntiholomorphicContraction.Dolbeault.covectorContraction (n + 1) w a) +
      AntiholomorphicContraction.Dolbeault.covectorContraction n w (AntiholomorphicContraction.Dolbeault.covectorContraction (n + 1) v a) = 0 := by
  have h := covectorContraction_same n (v + w) a
  rw [covectorContraction_add_direction n v w,
    covectorContraction_add_direction (n + 1) v w a, map_add, map_add,
    covectorContraction_same, covectorContraction_same, zero_add, add_zero] at h
  exact h

variable [NormedSpace ℂ E]

theorem antiContraction_squared (n : ℕ) (v : E)
    (a : E [⋀^Fin (n + 2)]→L[ℝ] ℂ) :
    AntiholomorphicContraction.Dolbeault.antiContraction n v (AntiholomorphicContraction.Dolbeault.antiContraction (n + 1) v a) = 0 := by
  have hcross := covectorContraction_anticommute n v (Complex.I • v) a
  have hneg := eq_neg_of_add_eq_zero_left hcross
  simp only [AntiholomorphicContraction.Dolbeault.antiContraction, _root_.smul_apply, _root_.add_apply,
    map_smul, map_add, covectorContraction_same]
  rw [hneg]
  module

end

/-! Distinct constant antiholomorphic contractions anticommute. -/

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]

theorem antiContraction_add_direction (n : ℕ) (v w : E) (a : E [⋀^Fin (n + 1)]→L[ℝ] ℂ) :
    AntiholomorphicContraction.Dolbeault.antiContraction n (v + w) a = AntiholomorphicContraction.Dolbeault.antiContraction n v a + AntiholomorphicContraction.Dolbeault.antiContraction n w a := by
  simp only [AntiholomorphicContraction.Dolbeault.antiContraction, _root_.smul_apply, _root_.add_apply,
    smul_add, covectorContraction_add_direction]
  module

theorem antiContraction_anticommute (n : ℕ) (v w : E) (a : E [⋀^Fin (n + 2)]→L[ℝ] ℂ) :
    AntiholomorphicContraction.Dolbeault.antiContraction n v (AntiholomorphicContraction.Dolbeault.antiContraction (n + 1) w a) +
      AntiholomorphicContraction.Dolbeault.antiContraction n w (AntiholomorphicContraction.Dolbeault.antiContraction (n + 1) v a) = 0 := by
  have h := antiContraction_squared n (v + w) a
  rw [antiContraction_add_direction n v w,
    antiContraction_add_direction (n + 1) v w a, map_add, map_add,
    antiContraction_squared, antiContraction_squared, zero_add, add_zero] at h
  exact h

theorem antiContraction_preserves_kernel (n : ℕ) (v w : E) (a : E [⋀^Fin (n + 2)]→L[ℝ] ℂ)
    (ha : AntiholomorphicContraction.Dolbeault.antiContraction (n + 1) v a = 0) :
    AntiholomorphicContraction.Dolbeault.antiContraction n v (AntiholomorphicContraction.Dolbeault.antiContraction (n + 1) w a) = 0 := by
  have h := antiContraction_anticommute n v w a
  rwa [ha, map_zero, add_zero] at h

end

end OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContractionAnticommutation.Dolbeault
