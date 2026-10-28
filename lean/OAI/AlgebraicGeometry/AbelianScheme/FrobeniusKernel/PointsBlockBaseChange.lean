import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IntrinsicBlockBaseChange

/-! # Points Block Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsBlockBaseChange.Construction

noncomputable section

/-! The Frobenius map on the original CMPoints block is its native relative
Frobenius followed by the exact block pullback comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
variable (k : Type) [Field k] [CharP k q] [IsAlgClosed k] {g : ℕ}
variable (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)

local notation "hchar" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Affine.Construction.prime_eq_zero_spec q k (CharP.cast_eq_zero k q)
local notation "sF" => OAI.AlgebraicGeometry.Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q (Fact.out : q.Prime) (Spec (CommRingCat.of k)) hchar
local notation "AF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAbelian (q := q) k A
local notation "ρF" => OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTransport.Construction.l45FrobeniusTargetAction (q := q) k A ρ

omit [IsAlgClosed k] in
theorem l45FrobeniusBlockMap_eq_baseChange (n : ℕ) (τ : Gal(E/ℚ)) :
    (CMPointsTransport.Construction.l45FrobeniusBlockMap j iota hsplit k A ρ n τ).hom.hom =
      Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q (Fact.out : q.Prime) hchar
        (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X ≫
          (IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso j iota hsplit A ρ sF n τ).hom.hom.hom := by
  have : IsClosedImmersion (CMPointsAt.Construction.l45BlockInclusion j iota hsplit AF ρF n τ).left :=
    PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion_closed AF ρF _ _
  have : Mono (CMPointsAt.Construction.l45BlockInclusion j iota hsplit AF ρF n τ) := Over.mono_of_mono_left _
  apply (cancel_mono (CMPointsAt.Construction.l45BlockInclusion j iota hsplit AF ρF n τ)).mp
  have hl := CMPointsTransport.Construction.l45FrobeniusBlockMap_inclusion j iota hsplit k A ρ n τ
  have hb := IntrinsicBlockBaseChange.Construction.l45NativeBlockBaseChangeIso_inclusion j iota hsplit A ρ sF n τ
  have hn := (Picard.Homomorphisms.Group.Construction.relativeFrobeniusNat q (Fact.out : q.Prime) hchar).naturality
    (CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ n τ)
  exact hl.trans (hn.trans ((congrArg (fun z =>
    Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q (Fact.out : q.Prime) hchar
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ n τ).X ≫ z) hb.symm).trans
        (Category.assoc _ _ _).symm))

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PointsBlockBaseChange.Construction
