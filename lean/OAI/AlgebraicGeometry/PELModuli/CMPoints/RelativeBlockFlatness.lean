import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlockRetraction
import OAI.AlgebraicGeometry.PELModuli.CMPoints.FiniteGroupPresentation
import OAI.AlgebraicGeometry.PELModuli.CMPoints.FiniteFlatRetract

/-! # Relative Block Flatness -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeBlockFlatness

noncomputable section

/-! Relative finite local freeness of the actual coefficient blocks is a
consequence of finite local freeness of the ambient abelian torsion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem split_block_finite_locally_free
    {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
    (j : Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
    {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
    (n : ℕ) (τ : Gal(E/ℚ))
    [IsFinite (A.torsionScheme (q ^ n)).hom]
    [Flat (A.torsionScheme (q ^ n)).hom]
    [LocallyOfFinitePresentation (A.torsionScheme (q ^ n)).hom] :
    let B := BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ
    IsFinite B.X.hom ∧ Flat B.X.hom ∧ LocallyOfFinitePresentation B.X.hom := by
  let B := BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ
  let : IsFinite B.X.hom := FiniteGroupPresentation.idempotentBlock_finite A ρ (q ^ n) (j.projector iota hsplit n τ)
  have h := FiniteFlatRetract.finite_flat_scheme_retract_general (BlockRetraction.actualTorsionGroup (q := q) A n).X B.X
    (BlockRetraction.blockToTorsionGroup j iota hsplit A ρ n τ).hom.hom
    (BlockRetraction.torsionToBlockGroup j iota hsplit A ρ n τ).hom.hom
    (BlockRetraction.block_scheme_retraction j iota hsplit A ρ n τ)
  exact ⟨inferInstance, h.1, h.2⟩

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeBlockFlatness
