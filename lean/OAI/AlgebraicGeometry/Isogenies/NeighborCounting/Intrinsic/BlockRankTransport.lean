import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralIntrinsicBlock
import OAI.AlgebraicGeometry.PELModuli.CMPoints.RelativeBlockRank
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsBlockHeightIso
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.BaseChange

/-! # Block Rank Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockRankTransport

noncomputable section

/-! Native block ranks commute with the actual scalar extension and
with an equivariant isomorphism of the original polarized source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.IntegralIntrinsicBlock.Intrinsic

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme.{0}} {g N : ℕ} {δ : Fin g → ℕ}
  (PA : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PA.abelian)
  (n : ℕ) (τ : Gal(E/ℚ))

theorem nativeBlock_baseChange_rank {S' : Scheme.{0}} (f : S' ⟶ S) (z : S') :
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) ((ρ.pullback f).map (j.projector iota hsplit n τ))).hom.finrank z =
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ))).hom.finrank (f z) := by
  obtain ⟨hf, hflat, _⟩ := IntegralIntrinsicBlock.Intrinsic.integralCMPointsBlock_finiteLocallyFree j iota hsplit PA ρ n τ
  let : IsFinite (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PA.abelian ρ n τ).X.hom := hf
  let : Flat (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PA.abelian ρ n τ).X.hom := hflat
  exact (IntegralIntrinsicBlock.Intrinsic.integralNativeBlock_rank j iota hsplit (PA.pullback f) (ρ.pullback f) n τ z).trans
    ((PELModuli.CMPoints.RelativeBlockRank.split_block_baseChange_rank j iota hsplit PA.abelian ρ n τ f z).trans
      (IntegralIntrinsicBlock.Intrinsic.integralNativeBlock_rank j iota hsplit PA ρ n τ (f z)).symm)

variable (PB : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PB.abelian)
  (e : PA.abelian.scheme ≅ PB.abelian.scheme) [IsMonHom e.hom]
  (he : ∀ a : NumberField.RingOfIntegers E, ρ.map a ≫ e.hom = e.hom ≫ σ.map a)

def originalBlockSourceIso :
    (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PA.abelian ρ n τ).toGrp ≅
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PB.abelian σ n τ).toGrp :=
  (yonedaGrpFullyFaithful (C := Over S)).preimageIso
    (AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit PA.abelian ρ n τ ≪≫
      AbelianScheme.FrobeniusKernel.PointsBlockHeightIso.Construction.l45BlockFunctorIso PA.abelian PB.abelian ρ σ e he (j.localCharacter iota τ) n ≪≫
        (AbelianScheme.FrobeniusKernel.CMPointsBlockRepresentation.Construction.l45BlockYonedaIso j iota hsplit PB.abelian σ n τ).symm)

include e he in
theorem nativeBlock_sourceIso_rank (z : S) :
    (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (ρ.map (j.projector iota hsplit n τ))).hom.finrank z =
      (AbelianScheme.IsogenyQuotient.OppositeKernel.Construction.torsionBlock (q ^ n) (σ.map (j.projector iota hsplit n τ))).hom.finrank z := by
  obtain ⟨hf, hflat, _⟩ := IntegralIntrinsicBlock.Intrinsic.integralCMPointsBlock_finiteLocallyFree j iota hsplit PB σ n τ
  let : IsFinite (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PB.abelian σ n τ).X.hom := hf
  let : Flat (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PB.abelian σ n τ).X.hom := hflat
  let f : (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PA.abelian ρ n τ).X ≅
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit PB.abelian σ n τ).X :=
    (Grp.forget _).mapIso (originalBlockSourceIso j iota hsplit PA ρ n τ PB σ e he)
  have : IsIso f.hom.left := (Over.forget _).map_isIso f.hom
  refine (IntegralIntrinsicBlock.Intrinsic.integralNativeBlock_rank j iota hsplit PA ρ n τ z).trans
    (Eq.trans ?_ (IntegralIntrinsicBlock.Intrinsic.integralNativeBlock_rank j iota hsplit PB σ n τ z).symm)
  erw [← f.hom.w]
  exact congrFun (Scheme.Hom.finrank_comp_left_of_isIso f.hom.left _) z

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.BlockRankTransport
