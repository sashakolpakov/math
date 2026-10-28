import OAI.AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors

/-! # CM Points Block Representation -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation.Construction

noncomputable section

/-! The native CMPoints equalizer block represents the exact character-block
functor on every test scheme. This representation is independent of
the ordinary splitting and the Cartier-coordinate construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

def l45BlockYonedaIso (n : ℕ) (τ : Gal(E/ℚ)) :
    yonedaGrp.obj (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp ≅
      PELModuli.CMPoints.BlocksProjectors.blockFunctor A ρ (j.localCharacter iota τ) n :=
  yonedaGrpObjIsoOfRepresentableBy
    (PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A ρ (q ^ n) (j.projector iota hsplit n τ))
    (PELModuli.CMPoints.BlocksProjectors.blockFunctor A ρ (j.localCharacter iota τ) n)
    (PELModuli.CMPoints.BlocksProjectors.splitBlockRepresentable j iota hsplit A ρ n τ)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation.Construction
