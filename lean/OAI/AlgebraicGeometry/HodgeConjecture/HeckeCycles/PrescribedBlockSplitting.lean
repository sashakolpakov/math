import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DerivedBlockSplitting
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BlockSignature
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ZeroBlockSplitting

/-! # Prescribed Block Splitting -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrescribedBlockSplitting.CM

noncomputable section

/-! Construct the original ordinary coefficient block with precisely
the factors forced by its full CMPoints height and original PEL Lie rank,
at every finite torsion level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k E K : Type} [Field k] [IsAlgClosed k] [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime] [CharP k q]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {g N : ℕ} {δ : Fin g → ℕ} (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (τ : Gal(E/ℚ)) (h ℓ : ℕ)

theorem splitting
    (hordinary : Nat.card (A.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
    (hheight : PELModuli.CMPoints.BlocksProjectors.BlockHasHeight A.abelian ρ (j.localCharacter iota τ) h)
    (hlie : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A.abelian ρ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) ℓ)
    (n : ℕ) : Nonempty (AbelianScheme.FrobeniusKernel.OrdinaryBlocks.Construction.OrdinaryBlockSplitting k
      (PELModuli.CMPoints.BlocksProjectors.splitBlockGroupScheme j iota hsplit A.abelian ρ n τ).toGrp q n ℓ (h - ℓ)) := by
  cases n with
  | zero => exact ⟨ZeroBlockSplitting.CM.splitting j iota hsplit A.abelian ρ τ ℓ (h - ℓ)⟩
  | succ n =>
    let : IsFinite (A.abelian.torsionScheme (q ^ (n + 1))).hom :=
      Ordinary.TorsionFinite.CM.torsion_finite A.abelian q hordinary (n + 1)
    obtain ⟨d, r, ⟨e⟩⟩ := DerivedBlockSplitting.CM.exists_splitting j iota hsplit A ρ hordinary n τ
    exact (BlockSignature.CM.prescribed j iota hsplit A.abelian ρ τ n h ℓ hheight hlie e).2

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PrescribedBlockSplitting.CM
