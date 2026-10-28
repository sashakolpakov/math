import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProjectivePELFineConstruction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompatiblePureFineConstruction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ArithmeticRefinement

/-! # Refinement From Auxiliary Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RefinementFromAuxiliaryModel

noncomputable section

/-! A single actual quasi-projective pure fine model at an auxiliary
level at least three supplies the cofinal arithmetic-level construction.
No assertion about moduli at other bases or unrelated levels is an input.
The prescribed levels are multiples of the supplied auxiliary level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_quasiProjective_fine_arithmetic_level_refinement_from_auxiliaryModel
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [Field K] [NumberField K] {s L : ℕ} (P : Datum.RankThreePELDatum E s) (iota : E →+* K)
    (hP : P.IsAdmissible)
    (A : Pure.Fine.PurePolarizedModel (3 * s) P.polarizationType L (Spec (.of K)))
    (hA : A.IsFine) (hL : 3 ≤ L) (Q : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation A.space)
    (H : OpenSubgroup P.FiniteSpecialUnitary) (M : ℕ) (hM : 0 < M) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ M ∣ N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N →
      (∀ g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice N g →
        LinearMap.det g.toLinearMap = 1) ∧
      P.adelicPrincipalLevel N ≤ H.toSubgroup ∧
      ∃ Γ : Subgroup (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E),
        (∀ g, g ∈ Γ ↔ NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice N g ∧ LinearMap.det g.toLinearMap = 1) ∧
        (∀ g ∈ Γ, ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1) ∧
        ∃ F : Models.FinePELModel P iota N,
          F.IsFine ∧ Nonempty (HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation F.space) := by
  have : Countable K := NumberFieldCountability.numberField_countable K
  obtain ⟨N₀, h3, hML, hdeep⟩ := ArithmeticRefinement.exists_arithmetic_level_refinement P hP H (M * L)
    (Nat.mul_pos hM (lt_of_lt_of_le (by decide : 0 < 3) hL))
  refine ⟨N₀, h3, (dvd_mul_right M L).trans hML, ?_⟩
  intro N hN hdiv
  obtain ⟨hdet, hH, Γ, hΓ, hfree⟩ := hdeep N hN hdiv
  refine ⟨hdet, hH, Γ, hΓ, hfree, ?_⟩
  have hLN : L ∣ N := (dvd_mul_left L M).trans (hML.trans hdiv)
  obtain ⟨k, rfl⟩ := hLN
  have hk : k ≠ 0 := by
    intro hk
    simp only [hk, Nat.mul_zero, lt_self_iff_false] at hN
  let : NeZero L := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) hL)⟩
  let : NeZero k := ⟨hk⟩
  obtain ⟨B, hB, ⟨QB⟩⟩ :=
    A.exists_quasiProjective_fine_pure_model_at_multiple (k := k) hA hL Q
  exact ProjectivePELFineConstruction.exists_quasiProjective_fine_pel_model_of_fine_pure P iota B QB hB
    (h3.trans (Nat.le_of_dvd hN hdiv))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RefinementFromAuxiliaryModel
