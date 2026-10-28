import OAI.AlgebraicGeometry.PELModuli.CMPoints.ConjugateProjectors
import OAI.AlgebraicGeometry.PELModuli.CMPoints.CharacterRetracts
import OAI.AlgebraicGeometry.PELModuli.CMPoints.DualityPairing

/-! # Block Polarization -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockPolarization

noncomputable section

/-! The polarization pairing restricts to Cartier duality between the
two conjugate coefficient blocks. The only pairing input concerns the
ambient abelian scheme; block perfection follows from its projectors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
  (P : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) P.abelian)

theorem polarization_character_projectors (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation P ρ)
    (n : ℕ) (e : DualityPairing.TorsionCharacterIso P (q ^ n))
    (he : DualityPairing.TorsionCharacterAdjoint P (q ^ n) e) (τ : Gal(E/ℚ)) :
    Functor.whiskerRight
      (BlockRetraction.torsionProjectionNat j iota hsplit P.abelian ρ n (Arithmetic.rationalConjugation E * τ) ≫
        BlocksProjectors.blockInclusion P.abelian ρ (j.localCharacter iota (Arithmetic.rationalConjugation E * τ)) n)
      (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫
      (Functor.whiskerRight (DualityPairing.polarizationOnTorsion P (q ^ n))
        (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫ e.hom) =
    (Functor.whiskerRight (DualityPairing.polarizationOnTorsion P (q ^ n))
        (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫ e.hom) ≫
      DualityPairing.restrictCharacters (BlockRetraction.torsionProjectionNat j iota hsplit P.abelian ρ n τ ≫
        BlocksProjectors.blockInclusion P.abelian ρ (j.localCharacter iota τ) n) := by
  rw [← ConjugateProjectors.conjugate_projector_on_torsion, ConjugateProjectors.torsionProjection_inclusion]
  exact DualityPairing.polarization_character_adjoint P ρ hρ (q ^ n) e he (j.projector iota hsplit n τ)

include hsplit in
theorem conjugate_block_pairing_isIso (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation P ρ)
    (n : ℕ) (e : DualityPairing.TorsionCharacterIso P (q ^ n))
    (he : DualityPairing.TorsionCharacterAdjoint P (q ^ n) e)
    [IsIso (Functor.whiskerRight (DualityPairing.polarizationOnTorsion P (q ^ n))
      (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫ e.hom)] (τ : Gal(E/ℚ)) :
    IsIso (Functor.whiskerRight
        (BlocksProjectors.blockInclusion P.abelian ρ (j.localCharacter iota (Arithmetic.rationalConjugation E * τ)) n ≫
          DualityPairing.polarizationOnTorsion P (q ^ n)) (forget GrpCat ⋙ uliftFunctor.{1, 0}) ≫
      e.hom ≫ DualityPairing.restrictCharacters (BlocksProjectors.blockInclusion P.abelian ρ (j.localCharacter iota τ) n)) := by
  let U := forget GrpCat ⋙ uliftFunctor.{1, 0}
  let eA := asIso (Functor.whiskerRight (DualityPairing.polarizationOnTorsion P (q ^ n)) U ≫ e.hom)
  let iB := Functor.whiskerRight
    (BlocksProjectors.blockInclusion P.abelian ρ (j.localCharacter iota (Arithmetic.rationalConjugation E * τ)) n) U
  let rB := Functor.whiskerRight
    (BlockRetraction.torsionProjectionNat j iota hsplit P.abelian ρ n (Arithmetic.rationalConjugation E * τ)) U
  have hB : iB ≫ rB = 𝟙 _ := by
    dsimp only [iB, rB]
    rw [← Functor.whiskerRight_comp, BlockRetraction.blockInclusion_projection]
    ext T x
    rfl
  have hadj : (rB ≫ iB) ≫ eA.hom = eA.hom ≫
      DualityPairing.restrictCharacters (BlockRetraction.torsionProjectionNat j iota hsplit P.abelian ρ n τ ≫
        BlocksProjectors.blockInclusion P.abelian ρ (j.localCharacter iota τ) n) := by
    dsimp only [rB, iB, eA, asIso_hom]
    rw [← Functor.whiskerRight_comp]
    exact polarization_character_projectors j iota hsplit P ρ hρ n e he τ
  let eB := CharacterRetracts.characterBlockIso _ eA _ iB rB hB
    (BlocksProjectors.blockInclusion P.abelian ρ (j.localCharacter iota τ) n)
    (BlockRetraction.torsionProjectionNat j iota hsplit P.abelian ρ n τ)
    (BlockRetraction.blockInclusion_projection j iota hsplit P.abelian ρ n τ) hadj
  have hh : eB.hom = Functor.whiskerRight
        (BlocksProjectors.blockInclusion P.abelian ρ (j.localCharacter iota (Arithmetic.rationalConjugation E * τ)) n ≫
          DualityPairing.polarizationOnTorsion P (q ^ n)) U ≫ e.hom ≫
      DualityPairing.restrictCharacters (BlocksProjectors.blockInclusion P.abelian ρ (j.localCharacter iota τ) n) := by
    change (iB ≫ eA.hom ≫ _) = _
    dsimp only [iB, eA, asIso_hom]
    rw [Functor.whiskerRight_comp]
    simp only [Category.assoc]
  exact (congrArg IsIso hh).mp (inferInstanceAs (IsIso eB.hom))

include hsplit in
theorem polarizationDuality_of_ambient_pairing (hPair : DualityPairing.PolarizedTorsionCartierInput)
    (hρ : AbelianModuli.ReferenceFamily.ActionData.RosatiConjugation P ρ) (hgood : q.Coprime (∏ i, δ i))
    (τ : Gal(E/ℚ)) :
    DualityPairing.PolarizationDuality P ρ (j.localCharacter iota τ)
      (j.localCharacter iota (Arithmetic.rationalConjugation E * τ)) := by
  intro n
  obtain ⟨e, headd, headj, heiso⟩ := hPair S g δ N P (q ^ n)
    (pow_pos (Fact.out : q.Prime).pos n) (hgood.pow_left n)
  let := heiso
  refine ⟨e, headd, ?_, conjugate_block_pairing_isIso j iota hsplit P ρ hρ n e headj τ⟩
  intro a
  obtain ⟨d, hd, hp, _⟩ := hρ a
  let := hd
  exact ⟨d, hd, hp, headj (ρ.map a) inferInstance d hd hp⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockPolarization
