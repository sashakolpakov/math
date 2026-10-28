import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EtaleTangents
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockLieCharacter
import OAI.RepresentationTheory.Hecke.LieRankZero
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt

/-! # Block Lie Equiv -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockLieEquiv.CM

noncomputable section

/-! Identify the original coefficient block's actual tangent points with
the original PEL Lie eigenspace. The inverse is its integral projector lift. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt.Construction

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TangentRank.CM

variable {k E K : Type} [Field k] [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime] [CharP k q]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (τ : Gal(E/ℚ)) (n : ℕ)

local instance inclusion_mono : Mono (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ (n + 1) τ) :=
  inferInstanceAs (Mono (PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion A ρ (q ^ (n + 1))
    (j.projector iota hsplit (n + 1) τ)))

def lift (x : AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ)) :
    AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k ⟶ (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ).X :=
  (PELModuli.CMPoints.BlocksProjectors.idempotentBlockPointsEquiv A ρ (q ^ (n + 1))
    (j.projector iota hsplit (n + 1) τ) (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k)).symm
    ⟨x.val, by
      rw [pow_succ', pow_mul, RepresentationTheory.Hecke.LieRankZero.OrdinaryCharacterIntrinsic.lieEigenpoint_pow_char A ρ _ q x, one_pow],
      (x.property.2 (j.projector iota hsplit (n + 1) τ)).trans (by
        rw [BlockLieCharacter.CM.character_projector j iota τ hsplit n,
          RepresentationTheory.Hecke.LieRankZero.OrdinaryCharacterIntrinsic.dualNumberScalar_one, Category.id_comp])⟩

theorem lift_inclusion (x : AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ)) :
    lift j iota hsplit A ρ τ n x ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ (n + 1) τ = x.val :=
  congrArg Subtype.val ((PELModuli.CMPoints.BlocksProjectors.idempotentBlockPointsEquiv A ρ (q ^ (n + 1))
    (j.projector iota hsplit (n + 1) τ) (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k)).apply_symm_apply _)

def fromLie (x : AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ)) :
    TangentRank.CM.Points (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ).toGrp :=
  ⟨lift j iota hsplit A ρ τ n x, by
    apply (cancel_mono (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ (n + 1) τ)).mp
    rw [Category.assoc, lift_inclusion, x.property.1, MonObj.one_comp]⟩

variable {d : ℕ}
  (hr : TangentRank.CM.HasRank (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ).toGrp d)

def toLie (x : TangentRank.CM.Points (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ).toGrp) :
    AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) :=
  ⟨x.val ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ (n + 1) τ, by
    constructor
    · rw [← Category.assoc, x.property, MonObj.one_comp]
    · intro a
      let B := PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ
      let : IsCommMonObj B.toGrp.X := B.comm
      have hs := TangentRank.CM.scalar_nat hr x (j.residueCharacter iota τ (n + 1) a).val
      have hi := AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion_scalar j iota hsplit A ρ (n + 1) τ a
        (AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest k) x.val
      calc
        (x.val ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ (n + 1) τ) ≫ ρ.map a =
            (x.val ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ (n + 1) τ) ^
              (j.residueCharacter iota τ (n + 1) a).val := hi
        _ = (x.val ^ (j.residueCharacter iota τ (n + 1) a).val) ≫
            AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ (n + 1) τ := (MonObj.pow_comp _ _ _).symm
        _ = (AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar k ((j.residueCharacter iota τ (n + 1) a).val : k) ≫ x.val) ≫
            AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ (n + 1) τ := congrArg (· ≫ _) hs.symm
        _ = _ := by rw [← BlockLieCharacter.CM.character_nat j iota τ n a, Category.assoc]⟩

def lieEquiv : TangentRank.CM.Points (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ).toGrp ≃
    AbelianModuli.ReferenceFamily.LieRanks.LieEigenpoints A ρ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) where
  toFun := toLie j iota hsplit A ρ τ n hr
  invFun := fromLie j iota hsplit A ρ τ n
  left_inv x := by
    apply Subtype.ext
    apply (cancel_mono (AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ (n + 1) τ)).mp
    exact lift_inclusion j iota hsplit A ρ τ n _
  right_inv x := Subtype.ext (lift_inclusion j iota hsplit A ρ τ n x)

include hr in
theorem hasLieRank : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) d := by
  obtain ⟨e, ha, hs⟩ := hr
  let h : TangentRank.CM.HasRank (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ).toGrp d := ⟨e, ha, hs⟩
  refine ⟨e.trans (lieEquiv j iota hsplit A ρ τ n h), ?_, ?_⟩
  · intro x y
    change (e (x + y)).val ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ (n + 1) τ = _
    rw [ha, MonObj.mul_comp]
    rfl
  · intro a x
    change (e (a • x)).val ≫ AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ (n + 1) τ = _
    rw [hs, Category.assoc]
    rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockLieEquiv.CM
