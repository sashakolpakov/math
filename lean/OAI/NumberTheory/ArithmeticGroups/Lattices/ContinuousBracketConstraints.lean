import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousJacobi
import OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousBracketChange

/-! # Continuous Bracket Constraints -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousBracketConstraints.Construction

noncomputable section

/-! Alternation and Jacobi form one system of bracket equations.
Its linearization has a quadratic remainder at every Lie bracket. -/

variable {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L] [FiniteDimensional ℝ L]

local instance constraintEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance constraintEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance constraintBilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance constraintBilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance constraintBilinear_finite : FiniteDimensional ℝ (L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance constraintTrilinear_normed : NormedAddCommGroup (L →L[ℝ] L →L[ℝ] L →L[ℝ] L) := inferInstance
local instance constraintTrilinear_space : NormedSpace ℝ (L →L[ℝ] L →L[ℝ] L →L[ℝ] L) := inferInstance

def continuousAlternationDefect : (L →L[ℝ] L →L[ℝ] L) →L[ℝ] (L →L[ℝ] L →L[ℝ] L) :=
  ContinuousLinearMap.id ℝ _ +
    (ContinuousLinearMap.flipₗᵢ ℝ L L L).toContinuousLinearEquiv.toContinuousLinearMap

omit [FiniteDimensional ℝ L] in
theorem continuousAlternationDefect_apply (B : L →L[ℝ] L →L[ℝ] L) (x y : L) :
    continuousAlternationDefect B x y = B x y + B y x := rfl

omit [FiniteDimensional ℝ L] in
theorem continuousAlternationDefect_eq_zero (B : L →L[ℝ] L →L[ℝ] L) :
    continuousAlternationDefect B = 0 ↔ ∀ x, B x x = 0 := by
  constructor
  · intro h x
    have he := congrArg (fun C : L →L[ℝ] L →L[ℝ] L => C x x) h
    change B x x + B x x = 0 at he
    have hs : (2 : ℝ) • B x x = 0 := by simpa only [two_smul] using he
    exact (smul_eq_zero.mp hs).resolve_left (by norm_num)
  · intro h
    ext x y
    have he := h (x + y)
    simp only [map_add, add_apply, h, zero_add, add_zero] at he
    simpa only [continuousAlternationDefect_apply, zero_apply, add_comm] using he

def IsContinuousLieBracket (B : L →L[ℝ] L →L[ℝ] L) : Prop :=
  (∀ x, B x x = 0) ∧ ContinuousJacobi.Construction.continuousJacobiPair B B = 0

def continuousBracketLinearization (B : L →L[ℝ] L →L[ℝ] L) :
    (L →L[ℝ] L →L[ℝ] L) →L[ℝ]
      (L →L[ℝ] L →L[ℝ] L) × (L →L[ℝ] L →L[ℝ] L →L[ℝ] L) :=
  continuousAlternationDefect.prod (ContinuousJacobi.Construction.continuousJacobiLinearization B)

theorem continuousBracketLinearization_eq_zero
    (B C : L →L[ℝ] L →L[ℝ] L) :
    continuousBracketLinearization B C = 0 ↔
      (∀ x, C x x = 0) ∧ ContinuousJacobi.Construction.continuousJacobiLinearization B C = 0 := by
  change (continuousAlternationDefect C, ContinuousJacobi.Construction.continuousJacobiLinearization B C) = (0, 0) ↔ _
  rw [Prod.mk.injEq, continuousAlternationDefect_eq_zero]

theorem continuousBracketLinearization_norm_bound
    (B C : L →L[ℝ] L →L[ℝ] L) (hB : IsContinuousLieBracket B)
    (hC : IsContinuousLieBracket (B + C)) :
    ‖continuousBracketLinearization B C‖ ≤ ‖ContinuousJacobi.Construction.continuousJacobiPair (L := L)‖ * ‖C‖ ^ 2 := by
  have hAlt : continuousAlternationDefect C = 0 := by
    apply (continuousAlternationDefect_eq_zero C).mpr
    intro x
    have he := hC.1 x
    simpa only [add_apply, hB.1, zero_add] using he
  change ‖(continuousAlternationDefect C, ContinuousJacobi.Construction.continuousJacobiLinearization B C)‖ ≤ _
  rw [hAlt, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  exact ContinuousJacobi.Construction.continuousJacobiLinearization_norm_bound B C hB.2 hC.2

theorem isContinuousLieBracket_change (e : L ≃L[ℝ] L) (B : L →L[ℝ] L →L[ℝ] L)
    (hB : IsContinuousLieBracket B) : IsContinuousLieBracket (ContinuousBracketChange.Construction.continuousBracketChange e B) := by
  refine ⟨ContinuousBracketChange.Construction.continuousBracketChange_alternating e B hB.1, ?_⟩
  exact (ContinuousJacobi.Construction.continuousJacobi_zero_iff _).mpr
    (ContinuousBracketChange.Construction.continuousBracketChange_jacobi e B ((ContinuousJacobi.Construction.continuousJacobi_zero_iff _).mp hB.2))

theorem isContinuousLieBracket_change_iff (e : L ≃L[ℝ] L) (B : L →L[ℝ] L →L[ℝ] L) :
    IsContinuousLieBracket (ContinuousBracketChange.Construction.continuousBracketChange e B) ↔ IsContinuousLieBracket B := by
  refine ⟨fun h => ?_, isContinuousLieBracket_change e B⟩
  have h' := isContinuousLieBracket_change e.symm (ContinuousBracketChange.Construction.continuousBracketChange e B) h
  rwa [ContinuousBracketChange.Construction.continuousBracketChange_inverse] at h'

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousBracketConstraints.Construction
