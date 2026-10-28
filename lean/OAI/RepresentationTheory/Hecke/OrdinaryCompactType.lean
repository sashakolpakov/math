import OAI.RepresentationTheory.Hecke.OrdinaryBlockGeometry
import OAI.RepresentationTheory.Hecke.EtaleLieRank
import OAI.RepresentationTheory.Hecke.MultiplicativeLieRank
import OAI.RepresentationTheory.Hecke.BlockCharacters
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt

/-! # Ordinary Compact Type -/

namespace OAI.RepresentationTheory.Hecke.OrdinaryCompactType.OrdinaryCharacterIntrinsic

noncomputable section

/-! The pure compact block type is forced by its prescribed Lie rank.
The etale case uses uniqueness of infinitesimal lifts. The multiplicative
case uses a nonzero dual-number point in the actual embedded block. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt.Construction

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : AlgebraicGeometry.PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {k : Type} [Field k] [CharP k q] {g : ℕ}
  (A : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (ρ : AlgebraicGeometry.AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) (τ : Gal(E/ℚ))

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

theorem pureEtale_hasLieRank_zero
    (e : AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
      (AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp q 1 0 3)
    {r : ℕ} (hr : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ (BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) r) : r = 0 := by
  have hg := OrdinaryBlockGeometry.OrdinaryCharacterIntrinsic.pureEtaleBlock_geometry k q 1 3 e
  have hf : IsFinite (AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A ρ (q ^ 1)
      (j.projector iota hsplit 1 τ)).hom := hg.1
  have he : Etale (AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A ρ (q ^ 1)
      (j.projector iota hsplit 1 τ)).hom := hg.2
  have : IsFinite (AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A ρ q (j.projector iota hsplit 1 τ)).hom :=
    (congrArg (fun n => IsFinite (AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A ρ n
      (j.projector iota hsplit 1 τ)).hom) (pow_one q)).mp hf
  have : Etale (AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A ρ q (j.projector iota hsplit 1 τ)).hom :=
    (congrArg (fun n => Etale (AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.idempotentBlockScheme A ρ n
      (j.projector iota hsplit 1 τ)).hom) (pow_one q)).mp he
  exact EtaleLieRank.OrdinaryCharacterIntrinsic.hasLieRank_eq_zero_of_etaleBlock A ρ (BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) q
    (j.projector iota hsplit 1 τ) (BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter_projector j iota τ hsplit) hr

theorem pureMultiplicative_not_hasLieRank_zero
    (e : AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
      (AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp q 1 3 0) :
    ¬ AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ (BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) 0 := by
  let m : OrdinaryCharacterDiagonalizableTangents.OrdinaryIntrinsic.DiagonalizableTangents.groupScheme (k := k)
      (M := AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockLabels q 1 3) ⟶ (AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).X :=
    (AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k e).hom.hom
  have : IsMonHom m := (AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k e).hom.isMonHom_hom
  have : Mono m := inferInstanceAs (Mono (AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.ordinaryMultiplicativeInclusion k e).hom.hom)
  let inc := AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion j iota hsplit A ρ 1 τ
  have : IsMonHom inc := AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion_isMonHom j iota hsplit A ρ 1 τ
  have : Mono inc := inferInstanceAs
    (Mono (AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.idempotentBlockInclusion A ρ (q ^ 1) (j.projector iota hsplit 1 τ)))
  let f := m ≫ inc
  have : IsMonHom f := inferInstance
  have : Mono f := inferInstance
  apply MultiplicativeLieRank.OrdinaryCharacterIntrinsic.not_hasLieRank_zero_of_multiplicative A ρ (BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) f
    (fun a => (j.residueCharacter iota τ 1 a).val) (BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter_nat j iota τ)
    (fun a T x => ?_) (BlockCharacters.OrdinaryCharacterIntrinsic.blockTangentCharacter_ne_zero (k := k) (q := q) (0 : Fin 3))
  have hs : ((x ≫ m) ≫ inc) ≫ ρ.map a =
      ((x ≫ m) ≫ inc) ^ (j.residueCharacter iota τ 1 a).val :=
    AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsAt.Construction.l45BlockInclusion_scalar j iota hsplit A ρ 1 τ a T (x ≫ m)
  have hx : (x ≫ m) ≫ inc = x ≫ f := Category.assoc _ _ _
  exact (congrArg (· ≫ ρ.map a) hx).symm.trans
    (hs.trans (congrArg (fun z => z ^ (j.residueCharacter iota τ 1 a).val) hx))

theorem ordinaryCompact_false_iff_lieRank_zero (c : Bool)
    (e : AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
      (AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp q 1
      (if c then 3 else 0) (if c then 0 else 3))
    {r : ℕ} (hr : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ (BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) r) :
    c = false ↔ r = 0 := by
  cases c with
  | false => exact ⟨fun _ => pureEtale_hasLieRank_zero j iota hsplit A ρ τ e hr, fun _ => rfl⟩
  | true =>
    constructor
    · intro h
      cases h
    · intro h
      subst r
      exact False.elim (pureMultiplicative_not_hasLieRank_zero j iota hsplit A ρ τ e hr)

theorem ordinaryCompact_eq_prescribed (c : Bool)
    (e : AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
      (AlgebraicGeometry.PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ 1 τ).toGrp q 1
      (if c then 3 else 0) (if c then 0 else 3))
    {r : ℕ} (hr : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ (BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) r) :
    c = decide (r ≠ 0) := by
  have h := ordinaryCompact_false_iff_lieRank_zero j iota hsplit A ρ τ c e hr
  by_cases hz : r = 0
  · simpa only [hz, ne_eq, not_true_eq_false, decide_false] using h.mpr hz
  · cases c with
    | false => exact False.elim (hz (h.mp rfl))
    | true => simp [hz]

end

end OAI.RepresentationTheory.Hecke.OrdinaryCompactType.OrdinaryCharacterIntrinsic
