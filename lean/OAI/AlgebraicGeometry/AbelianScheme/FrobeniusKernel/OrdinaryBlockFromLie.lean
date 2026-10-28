import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DerivedBlockSplitting
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockLieEquiv
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LieRankUniqueness

/-! # Ordinary Block From Lie -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlockFromLie.Construction

noncomputable section

/-! Source ordinarity and its existing Lie rank construct a splitting
with exactly that multiplicative dimension at any positive torsion level.
No block-height or compatibility of chosen splittings is required. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k E K : Type} [Field k] [IsAlgClosed k] [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime] [CharP k q]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (τ : Gal(E/ℚ)) (ell : ℕ)

theorem ordinaryBlock_splitting_of_lie
    (hordinary : Nat.card (A.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
    (hlie : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A.abelian ρ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) ell)
    (n : ℕ) :
    ∃ r : ℕ, Nonempty (OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A.abelian ρ (n + 1) τ).toGrp q (n + 1) ell r) := by
  obtain ⟨d, r, ⟨e⟩⟩ := HodgeConjecture.HeckeCycles.DerivedBlockSplitting.CM.exists_splitting j iota hsplit A ρ hordinary n τ
  have hd := HodgeConjecture.HeckeCycles.BlockLieEquiv.CM.hasLieRank j iota hsplit A.abelian ρ τ n
    (HodgeConjecture.HeckeCycles.EtaleTangents.CM.SplitTangentRank.ordinary_rank q n d r e)
  have he : d = ell := HodgeConjecture.HeckeCycles.LieRankUniqueness.CM.rank_unique A.abelian ρ _ hd hlie
  subst d
  exact ⟨r, ⟨e⟩⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlockFromLie.Construction
