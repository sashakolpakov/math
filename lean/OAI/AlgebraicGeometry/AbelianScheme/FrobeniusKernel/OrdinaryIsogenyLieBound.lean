import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SplitBlockLieBound
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryBlockFromLie
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Subgroup
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PolarizedIsogenyOrdinary

/-! # Ordinary Isogeny Lie Bound -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryIsogenyLieBound.Construction

noncomputable section

/-! An O_E-linear isogeny between ordinary polarized abelian varieties
cannot increase any original coefficient Lie rank. Both target splitting
and source cover are constructed from the given geometry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TangentRank.CM

variable {k E K : Type} [Field k] [IsAlgClosed k] [Field E] [NumberField E] [Algebra ℚ E]
  [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime] [CharP k q]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
  {g N M : ℕ} {δ ε : Fin g → ℕ}
  (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
  (B : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g ε M (Spec (.of k)))
  (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
  (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A.abelian B.abelian)
  (hσ : ∀ a, ρ.map a ≫ f.hom = f.hom ≫ σ.map a)
  (hordinary : Nat.card (A.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g)
  (n : ℕ)
  (hf : ∀ (T : Over (Spec (.of k))) (x : T ⟶ A.abelian.scheme), x ≫ f.hom = 1 → x ^ (q ^ n) = 1)

include hsplit hσ hordinary hf in
theorem ordinaryIsogeny_lieRank_le (τ : Gal(E/ℚ)) (ell : ℕ)
    (hlie : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A.abelian ρ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) ell) :
    ∃ d ≤ ell, AbelianModuli.ReferenceFamily.LieRanks.HasLieRank B.abelian σ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) d := by
  obtain ⟨rA, ⟨eA⟩⟩ := OrdinaryBlockFromLie.Construction.ordinaryBlock_splitting_of_lie j iota hsplit A ρ τ ell hordinary hlie n
  have hordB : Nat.card (B.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g :=
    (PolarizedIsogenyOrdinary.Construction.polarizedIsogeny_torsionCard_preserved A.abelian B.abelian A.dual A.polarization.isogeny
      f q (Fact.out : q.Prime).pos).symm.trans hordinary
  obtain ⟨dB, rB, ⟨eB⟩⟩ := HodgeConjecture.HeckeCycles.DerivedBlockSplitting.CM.exists_splitting j iota hsplit B σ hordB 0 τ
  exact ⟨dB, SplitBlockLieBound.Construction.splitBlockIsogeny_lieRank_le j iota hsplit A.abelian B.abelian ρ σ f hσ
    τ n hf eA eB⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryIsogenyLieBound.Construction
