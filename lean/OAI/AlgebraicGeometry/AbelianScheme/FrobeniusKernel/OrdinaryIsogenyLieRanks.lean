import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryIsogenyLieBound
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ComplementaryAction

/-! # Ordinary Isogeny Lie Ranks -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryIsogenyLieRanks.Construction

noncomputable section

/-! The constructed component bounds preserve every original ordinary
Lie rank by applying the bound to the actual complementary isogeny. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

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
theorem ordinaryIsogeny_preserves_blockLieRank (τ : Gal(E/ℚ)) (r : ℕ)
    (hr : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A.abelian ρ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) r) :
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank B.abelian σ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) r := by
  obtain ⟨c, hfc, hcf⟩ := ComplementaryIsogeny.Construction.exists_complementary_isogeny A.dual A.polarization.isogeny f
    (q ^ n) (pow_pos (Fact.out : q.Prime).pos n) hf
  have hordB : Nat.card (B.abelian.torsionPoints q (Over.mk (𝟙 (Spec (.of k))))) = q ^ g :=
    (PolarizedIsogenyOrdinary.Construction.polarizedIsogeny_torsionCard_preserved A.abelian B.abelian A.dual A.polarization.isogeny
      f q (Fact.out : q.Prime).pos).symm.trans hordinary
  obtain ⟨d, hd, hB⟩ := OrdinaryIsogenyLieBound.Construction.ordinaryIsogeny_lieRank_le j iota hsplit A B ρ σ f hσ hordinary n hf τ r hr
  obtain ⟨e, he, hA⟩ := OrdinaryIsogenyLieBound.Construction.ordinaryIsogeny_lieRank_le j iota hsplit B A σ ρ c
    (ComplementaryAction.Construction.complementaryIsogeny_action f c (q ^ n) ρ σ hσ hfc) hordB n
    (ComplementaryAction.Construction.complementaryIsogeny_kernel_killed f c (q ^ n) hcf) τ d hB
  have her : e = r := HodgeConjecture.HeckeCycles.LieRankUniqueness.CM.rank_unique A.abelian ρ _ hA hr
  have hdr : d = r := Nat.le_antisymm hd (her ▸ he)
  exact hdr ▸ hB

include hsplit hσ hordinary hf in
theorem ordinaryIsogeny_preserves_lieRanks (r : Gal(E/ℚ) → ℕ)
    (hr : ∀ τ, AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A.abelian ρ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) (r τ)) :
    ∀ τ, AbelianModuli.ReferenceFamily.LieRanks.HasLieRank B.abelian σ (RepresentationTheory.Hecke.BlockCharacters.OrdinaryCharacterIntrinsic.blockLieCharacter j iota τ) (r τ) :=
  fun τ => ordinaryIsogeny_preserves_blockLieRank j iota hsplit A B ρ σ f hσ hordinary n hf τ (r τ) (hr τ)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryIsogenyLieRanks.Construction
