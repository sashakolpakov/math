import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Generators
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveChart.Naturality

/-! # Evaluation Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.EvaluationTransport

noncomputable section

/-! Test projective chart surjectivity after identifying its target ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]

/-- Coordinates containing a generating family still generate the algebra. -/
theorem adjoin_range_eq_top_of_contains [Algebra R C] {ι κ : Type v}
    (v : ι → C) (w : κ → C) (hv : Algebra.adjoin R (Set.range v) = ⊤)
    (hvw : ∀ i, ∃ j, w j = v i) : Algebra.adjoin R (Set.range w) = ⊤ := by
  apply top_unique
  rw [← hv]
  apply Algebra.adjoin_mono
  rintro _ ⟨i, rfl⟩
  exact hvw i

/-- Surjectivity can be verified in an identified coordinate ring in which
the transported projective coordinates generate over the base. -/
theorem projectiveChartEvaluation_surjective_after_embedding [Algebra R C]
    (b : B →+* C) (hb : Function.Injective b) (c : R →+* B)
    (hc : b.comp c = algebraMap R C) {n : ℕ} (v : Fin (n + 1) → B)
    (i : Fin (n + 1)) (hi : v i = 1)
    (hv : Algebra.adjoin R (Set.range (fun j => b (v j))) = ⊤) :
    Function.Surjective (ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi) := by
  have h₁ : b (v i) = 1 := (congrArg b hi).trans b.map_one
  have hs := ProjectiveChart.Generators.projectiveChartEvaluation_surjective (R := R) (fun j => b (v j)) i h₁ hv
  have he : b.comp (ProjectiveChart.Evaluation.projectiveChartEvaluation c v i hi) =
      ProjectiveChart.Evaluation.projectiveChartEvaluation (algebraMap R C) (fun j => b (v j)) i h₁ := by
    simpa only [hc] using ProjectiveChart.Naturality.projectiveChartEvaluation_comp b c v i hi
  intro y
  obtain ⟨x, hx⟩ := hs (b y)
  exact ⟨x, hb ((RingHom.congr_fun he x).trans hx)⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Chart.EvaluationTransport
