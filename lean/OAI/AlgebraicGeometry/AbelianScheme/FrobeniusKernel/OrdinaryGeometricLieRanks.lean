import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryIsogenyAllCharacters
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryFieldExtension
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.IsogenyLieBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polarization.BaseChange

/-! # Ordinary Geometric Lie Ranks -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryGeometricLieRanks.Construction

noncomputable section

/-! The ordinary isogeny rank theorem applies on every geometric field,
with the original arithmetic residue character and the actual pulled-back action. -/

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
theorem ordinaryIsogeny_preserves_geometricLieRank
    {F : Type} [Field F] [IsAlgClosed F] (p : Spec (.of F) ⟶ Spec (.of k))
    (χ : NumberField.RingOfIntegers E →+* F) (r : ℕ)
    (hr : AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (A.abelian.pullback p) (ρ.pullback p) χ r) :
    AbelianModuli.ReferenceFamily.LieRanks.HasLieRank (B.abelian.pullback p) (σ.pullback p) χ r := by
  let c : k →+* F := (Spec.preimage p).hom
  let : CharP F q := charP_of_injective_ringHom c.injective q
  exact OrdinaryIsogenyAllCharacters.Construction.ordinaryIsogeny_preserves_characterLieRank j iota hsplit (A.pullback p) (B.pullback p)
    (ρ.pullback p) (σ.pullback p) (f.pullback p)
    (IsogenyLieBaseChange.Construction.isogenyAction_intertwines_baseChange f p ρ σ hσ)
    (OrdinaryFieldExtension.Construction.ordinary_torsionCard_fieldExtension A q hordinary p) n
    (IsogenyLieBaseChange.Construction.isogenyKernelBound_baseChange f p (q ^ n) hf) χ r hr

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.OrdinaryGeometricLieRanks.Construction
