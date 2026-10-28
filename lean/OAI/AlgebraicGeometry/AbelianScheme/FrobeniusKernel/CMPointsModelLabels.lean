import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ChosenLabels

/-! # CM Points Model Labels -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsModelLabels.Construction

noncomputable section

/-! The chosen-pair enumeration has exactly the dimension index of CMPoints. -/

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [IsGalois ℚ E] [NumberField.IsCMField E] [Field K] [NumberField K]

theorem exists_l45ModelLabels (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
    (chosen : Set Gal(E/ℚ)) (hc : PELModuli.CMPoints.Arithmetic.rationalConjugation E ∈ chosen)
    (hchosen : ∀ τ, τ ∈ chosen ↔ PELModuli.CMPoints.Arithmetic.rationalConjugation E * τ ∉ chosen) :
    ∃ labels : (Fin M.s × Bool) ≃ Gal(E/ℚ),
      labels (⟨0, hM.1⟩, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E ∧
      (∀ (v : Fin M.s) (b : Bool), labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b)) ∧
      (∀ v, labels (v, false) ∈ chosen) ∧
      (∀ v, labels (v, true) ∉ chosen) := by
  obtain ⟨s, e, he0, hec, hechosen, henot⟩ := ChosenLabels.Construction.exists_l45ChosenLabels chosen hc hchosen
  have hcard := Nat.card_congr e
  have hdegree := IsGalois.card_aut_eq_finrank ℚ E
  have hdimension := hM.2.1
  have hbool : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  have hsize : s + 1 = M.s := by
    simp only [Nat.card_prod, Nat.card_fin, hbool] at hcard
    omega
  let efin : Fin M.s ≃ Fin (s + 1) := finCongr hsize.symm
  let labels := (Equiv.prodCongr efin (Equiv.refl Bool)).trans e
  refine ⟨labels, ?_, ?_, ?_, ?_⟩
  · exact he0
  · intro v b
    cases b with
    | false => exact hec (efin v)
    | true =>
      change e (efin v, false) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * e (efin v, true)
      rw [hec, ← mul_assoc, PELModuli.CMPoints.Models.rationalConjugation_mul_self, one_mul]
  · intro v
    exact hechosen (efin v)
  · intro v
    exact henot (efin v)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsModelLabels.Construction
