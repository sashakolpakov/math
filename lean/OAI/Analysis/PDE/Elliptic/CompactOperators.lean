import OAI.Analysis.PDE.Elliptic.FiniteBasisCover
import Mathlib.Analysis.InnerProductSpace.Rayleigh

open Set InnerProductSpace Metric
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem norm_le_of_nonneg_quadratic (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) {L : ℝ} (hL : 0 ≤ L)
    (hlo : ∀ x, 0 ≤ inner ℝ x (A x))
    (hhi : ∀ x, inner ℝ x (A x) ≤ L * ‖x‖ ^ 2) : ‖A‖ ≤ L := by
  rw [A.norm_eq_iSup_rayleighQuotient hA]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simpa [hx] using hL
  have hx0 : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  change |inner ℝ (A x) x / ‖x‖ ^ 2| ≤ L
  rw [← real_inner_comm (A x) x, abs_of_nonneg (div_nonneg (hlo x) (sq_nonneg _))]
  exact (div_le_iff₀ hx0).mpr (hhi x)

omit [FiniteDimensional ℝ E] in
theorem isClosed_symmetric_operators :
    IsClosed {A : E →L[ℝ] E | A.toLinearMap.IsSymmetric} := by
  change IsClosed {A : E →L[ℝ] E | ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro y
  exact isClosed_eq ((continuous_id.clm_apply continuous_const).inner continuous_const)
    (continuous_const.inner (continuous_id.clm_apply continuous_const))

theorem isCompact_symmetric_norm_ball (L : ℝ) :
    IsCompact (closedBall (0 : E →L[ℝ] E) L ∩
      {A : E →L[ℝ] E | A.toLinearMap.IsSymmetric}) :=
  (isCompact_closedBall _ _).inter_right isClosed_symmetric_operators

/-- A bounded positive symmetric family has a finite collection of fixed
almost-diagonalizing bases. The bases depend only on the bound and tolerance. -/
theorem finite_basis_uniform_quadratic {L eps : ℝ} (hL : 0 ≤ L) (heps : 0 < eps) :
    ∃ bs : Finset (OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E),
      ∀ A : E →L[ℝ] E, A.toLinearMap.IsSymmetric →
        (∀ x, 0 ≤ inner ℝ x (A x)) →
        (∀ x, inner ℝ x (A x) ≤ L * ‖x‖ ^ 2) →
        ∃ b ∈ bs, A ∈ frameNeighborhood b eps := by
  obtain ⟨bs, hbs⟩ := finite_basis_cover (isCompact_symmetric_norm_ball (E := E) L)
    (fun _ h ↦ h.2) heps
  refine ⟨bs, ?_⟩
  intro A hA hlo hhi
  apply hbs A
  exact ⟨by simpa using norm_le_of_nonneg_quadratic A hA hL hlo hhi, hA⟩

end OAI.Analysis.PDE.Elliptic
