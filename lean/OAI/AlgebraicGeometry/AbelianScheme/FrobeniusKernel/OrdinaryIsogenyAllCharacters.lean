import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryIsogenyLieRanks
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.SplitResidueCharacters

/-! # Ordinary Isogeny All Characters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryIsogenyAllCharacters.Construction

noncomputable section

/-! Ordinary coefficient-linear isogenies preserve the actual Lie rank
for every residue character, independently of its split-coordinate label. -/

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
theorem ordinaryIsogeny_preserves_characterLieRank
    (χ : NumberField.RingOfIntegers E →+* k) (r : ℕ)
    (hr : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank A.abelian ρ χ r) : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank B.abelian σ χ r := by
  obtain ⟨τ, hτ⟩ := SplitResidueCharacters.Construction.exists_split_residueCharacter j iota hsplit χ
  subst χ
  exact OrdinaryIsogenyLieRanks.Construction.ordinaryIsogeny_preserves_blockLieRank j iota hsplit A B ρ σ f hσ hordinary n hf τ r hr

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryIsogenyAllCharacters.Construction
