import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockLieEquiv
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LieRankUniqueness
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockFactorHeights

/-! # Block Signature -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockSignature.CM

noncomputable section

/-! The full CMPoints height and original PEL Lie signature determine the
two dimensions of every constructed ordinary coefficient-block splitting. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k E K : Type} [Field k] [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime] [CharP k q]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A)
  (τ : Gal(E/ℚ)) (n : ℕ) [IsFinite (A.torsionScheme (q ^ (n + 1))).hom]

theorem dimensions (h ℓ : ℕ)
    (hheight : PELModuli.CMPoints.BlocksProjectors.BlockHasHeight A ρ (j.localCharacter iota τ) h)
    (hlie : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) ℓ)
    {d r : ℕ} (e : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ).toGrp q (n + 1) d r) :
    d = ℓ ∧ d + r = h := by
  have hd := BlockLieEquiv.CM.hasLieRank j iota hsplit A ρ τ n
    (EtaleTangents.CM.SplitTangentRank.ordinary_rank q n d r e)
  exact ⟨LieRankUniqueness.CM.rank_unique A ρ _ hd hlie,
    BlockFactorHeights.CM.sum_eq_height j iota hsplit A ρ τ h hheight n e⟩

theorem prescribed (h ℓ : ℕ)
    (hheight : PELModuli.CMPoints.BlocksProjectors.BlockHasHeight A ρ (j.localCharacter iota τ) h)
    (hlie : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A ρ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) ℓ)
    {d r : ℕ} (e : AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ).toGrp q (n + 1) d r) :
    ℓ ≤ h ∧ Nonempty (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A ρ (n + 1) τ).toGrp q (n + 1) ℓ (h - ℓ)) := by
  obtain ⟨hd, hs⟩ := dimensions j iota hsplit A ρ τ n h ℓ hheight hlie e
  subst d
  have hr : r = h - ℓ := by omega
  subst r
  exact ⟨by omega, ⟨e⟩⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockSignature.CM
