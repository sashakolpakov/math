import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsKernels
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.Cartier

/-! # CM Points Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTorsion.Construction

noncomputable section

/-!
The constructed native torsion decomposition proves finite local freeness
of the full source torsion. This supplies the finiteness needed for
ordinary q-rank preservation under the constructed isogenies.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
variable [Field K] [NumberField K] {κ : K →+* ℂ} {q : ℕ} [Fact q.Prime]
variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice K κ q) (iota : E →+* K)
variable (hsplit : j.HasSplitCoordinates iota)
variable {k : Type} [Field k] {g N : ℕ} {δ : Fin g → ℕ}
variable (PEL : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of k)))
variable (ρ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) PEL.abelian)
variable (n s : ℕ) (labels : (Fin s × Bool) ≃ Gal(E/ℚ))
variable (P : ∀ v : Fin s, CartierModel.Construction.CartierCoordinates (.of k)
  (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n))
variable (hdual : ∀ v : Fin s, PELModuli.CMPoints.DualityPairing.PolarizationDuality PEL ρ
  (j.localCharacter iota (labels (v, false))) (j.localCharacter iota (labels (v, true))))

include P hdual in
theorem l45FullTorsion_finiteLocallyFree :
    IsFinite (PEL.abelian.torsionScheme (q ^ n)).hom ∧
    Flat (PEL.abelian.torsionScheme (q ^ n)).hom ∧
    LocallyOfFinitePresentation (PEL.abelian.torsionScheme (q ^ n)).hom := by
  apply Cartier.Construction.group_finiteLocallyFree_of_iso
    (CMPointsSplitting.Construction.l45FullTorsionSplitting j iota hsplit PEL.abelian ρ n s labels)
  apply BlockProducts.Construction.groupBlockProduct_finiteLocallyFree
  intro v
  let G := CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) n
  let B := CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, true)) n
  have hG := (P v).group_finiteLocallyFree
  have hB := Cartier.Construction.group_finiteLocallyFree_of_iso
    (CMPointsAt.Construction.l45PairingAtLevel j iota hsplit PEL ρ (labels (v, false)) (labels (v, true)) (hdual v) n (P v))
    (P v).dualGroup_finiteLocallyFree
  have : IsFinite G.X.hom := hG.1
  have : Flat G.X.hom := hG.2.1
  have : LocallyOfFinitePresentation G.X.hom := hG.2.2
  have : IsFinite B.X.hom := hB.1
  have : Flat B.X.hom := hB.2.1
  have : LocallyOfFinitePresentation B.X.hom := hB.2.2
  change IsFinite (Limits.pullback.fst G.X.hom B.X.hom ≫ G.X.hom) ∧
    Flat (Limits.pullback.fst G.X.hom B.X.hom ≫ G.X.hom) ∧
    LocallyOfFinitePresentation (Limits.pullback.fst G.X.hom B.X.hom ≫ G.X.hom)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

variable [IsAlgClosed k]

include hdual in
theorem l45Isogeny_qRank_preserved
    (P₁ : ∀ v : Fin s, CartierModel.Construction.CartierCoordinates (.of k)
      (CMPointsAt.Construction.l45ChosenBlock j iota hsplit PEL ρ (labels (v, false)) 1))
    {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny PEL.abelian B) :
    Nat.card (PEL.abelian.torsionPoints q (Over.mk (𝟙 _))) =
      Nat.card (B.torsionPoints q (Over.mk (𝟙 _))) := by
  have hf : IsFinite (PEL.abelian.torsionScheme (q ^ 1)).hom :=
    (l45FullTorsion_finiteLocallyFree j iota hsplit PEL ρ 1 s labels P₁ hdual).1
  have : IsFinite (PEL.abelian.torsionScheme q).hom :=
    (congrArg (fun m => IsFinite (PEL.abelian.torsionScheme m).hom) (pow_one q)) ▸ hf
  exact OrdinaryQuotients.Construction.isogeny_qRank_preserved PEL.abelian B f q

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsTorsion.Construction
