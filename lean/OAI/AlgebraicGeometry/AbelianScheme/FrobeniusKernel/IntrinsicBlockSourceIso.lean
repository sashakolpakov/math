import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsBlockHeightIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsBlockPointsTransport

/-! # Intrinsic Block Source Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockSourceIso.Construction

noncomputable section

/-! An equivariant source isomorphism gives the native block isomorphism
with precisely the previously constructed block map as its forward map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable {S : Scheme} {g : ℕ} (A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
variable (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B)
variable (e : A.scheme ≅ B.scheme) [IsMonHom e.hom]
variable (he : ∀ z : NumberField.RingOfIntegers E, ρ.map z ≫ e.hom = e.hom ≫ σ.map z)
variable (n : ℕ) (τ : Gal(E/ℚ))

def l45NativeBlockSourceIso :
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).toGrp ≅
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit B σ n τ).toGrp :=
  (yonedaGrpFullyFaithful (C := Over S)).preimageIso
    (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit A ρ n τ ≪≫
      PointsBlockHeightIso.Construction.l45BlockFunctorIso A B ρ σ e he (j.localCharacter iota τ) n ≪≫
        (CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit B σ n τ).symm)

theorem l45NativeBlockSourceIso_hom :
    (l45NativeBlockSourceIso j iota hsplit A B ρ σ e he n τ).hom =
      PointsBlockPointsTransport.Construction.l45BlockMap j iota hsplit A B ρ σ e.hom he n τ := rfl

theorem l45NativeBlockSourceIso_inclusion :
    (l45NativeBlockSourceIso j iota hsplit A B ρ σ e he n τ).hom.hom.hom ≫
      CMPointsAt.Construction.l45BlockInclusion j iota hsplit B σ n τ =
      CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ n τ ≫ e.hom :=
  PointsBlockPointsTransport.Construction.l45BlockMap_inclusion j iota hsplit A B ρ σ e.hom he n τ

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockSourceIso.Construction
