import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicationCharacter.AffineRankOne
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.OfAffineRankOne

/-! # Line Bundles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual multiplication-character sheaves are line bundles: their affine sections descend from the proved constant-torsor character bases, and the descended rank-one modules produce local frames. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} [NeZero N]
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (level : A.FullLevel N)

def Abelian.Schemes.AbelianScheme.multiplicationCharacterLineBundle
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0) :
    Line.Bundles.LineBundle A.scheme.left := by
  have := A.multiplicationCharacterSheaf_quasicoherent level χ
  exact LineBundle.OfAffineRankOne.lineBundleOfAffineRankOne (A.multiplicationCharacterSheaf level χ)
    (A.multiplicationCharacter_affine_rankOne level χ hN)

theorem Abelian.Schemes.AbelianScheme.multiplicationCharacterLineBundle_sheaf
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0) :
    (A.multiplicationCharacterLineBundle level χ hN).sheaf = A.multiplicationCharacterSheaf level χ := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
