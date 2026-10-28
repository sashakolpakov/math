import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockPolarization
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierCharacterDuality

/-! # Cartier Duality Block Polarization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierDualityBlockPolarization

noncomputable section

/-! Restrict CartierDuality's actual canonical polarization pairing using the
proved conjugate coefficient projectors and their Poincare adjoints. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
  (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) P.abelian)

include hsplit in
theorem polarizationDuality_of_character_family
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation P ρ)
    (h : ∀ n : ℕ, ∃ e : DualityPairing.TorsionCharacterIso P (q ^ n),
      DualityPairing.TorsionCharacterAdditive P (q ^ n) e ∧ DualityPairing.TorsionCharacterAdjoint P (q ^ n) e ∧
      IsIso (Functor.whiskerRight (DualityPairing.polarizationOnTorsion P (q ^ n))
        (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫ e.hom))
    (τ : Gal(E/ℚ)) :
    DualityPairing.PolarizationDuality P ρ (j.localCharacter iota τ)
      (j.localCharacter iota (Arithmetic.rationalConjugation E * τ)) := by
  intro n
  obtain ⟨e, headd, headj, heiso⟩ := h n
  let := heiso
  refine ⟨e, headd, ?_, BlockPolarization.conjugate_block_pairing_isIso j iota hsplit P ρ hρ n e headj τ⟩
  intro a
  obtain ⟨d, hd, hp, _⟩ := hρ a
  let := hd
  exact ⟨d, hd, hp, headj (ρ.map a) inferInstance d hd hp⟩

include hsplit in
theorem polarizationDuality_of_native_CartierDuality
    {k : Type} [Field k] [IsAlgClosed k]
    (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) P.abelian)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation P ρ) (hgood : q.Coprime (∏ i, δ i))
    (τ : Gal(E/ℚ)) :
    DualityPairing.PolarizationDuality P ρ (j.localCharacter iota τ)
      (j.localCharacter iota (Arithmetic.rationalConjugation E * τ)) := by
  apply polarizationDuality_of_character_family j iota hsplit P ρ hρ _ τ
  intro n
  let hn := pow_pos (Fact.out : q.Prime).pos n
  exact ⟨CartierCharacterDuality.poincareTorsionCharacterIso P (q ^ n) hn,
    CartierCharacterDuality.poincareTorsionCharacter_additive P (q ^ n) hn,
    CartierCharacterDuality.poincareTorsionCharacter_adjoint P (q ^ n) hn,
    CartierCharacterDuality.poincareTorsionCharacter_perfect P (q ^ n) hn (hgood.pow_left n)⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.CartierDualityBlockPolarization
