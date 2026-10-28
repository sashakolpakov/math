import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.CharacterSheafQuasicoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.FromOpenSectionBases
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TameCharacters

/-! # Character Line Bundles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.CharacterLineBundles

noncomputable section

/-! Actual character sheaves of a constant tame torsor are line bundles, with local frames constructed from the proved section bases. This includes the exact ordered full-level group. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {S : Scheme.{u}} (c : K →+* Γ(S, ⊤))
    (G : Type u) [CommGroup G] [Fintype G]

def constantCharacterLineBundle [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (χ : G →* Kˣ) (hG : (Fintype.card G : K) ≠ 0) : Line.Bundles.LineBundle S := by
  letI := CharacterSheafQuasicoherence.constantCharacterSheaf_quasicoherent c G χ
  exact LineBundle.FromOpenSectionBases.lineBundleFromOpenSectionBases (CharacterSheafSections.constantCharacterSheaf c G χ)
    (CharacterSheafSections.constantCharacterSheafSectionsEquiv c G χ hG)

theorem constantCharacterLineBundle_sheaf [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (χ : G →* Kˣ) (hG : (Fintype.card G : K) ≠ 0) :
    (constantCharacterLineBundle c G χ hG).sheaf = CharacterSheafSections.constantCharacterSheaf c G χ := rfl

def fullLevelConstantCharacterLineBundle [IsAlgClosed K] (g N : ℕ) [NeZero N]
    (hN : (N : K) ≠ 0) (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) : Line.Bundles.LineBundle S := by
  have hG := TameCharacters.fullLevelCharacter_order_nonzero K g N hN
  have := TameCharacters.tameFiniteAbelian_hasEnoughRoots K _ hG
  exact constantCharacterLineBundle c _ χ hG

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.CharacterLineBundles
