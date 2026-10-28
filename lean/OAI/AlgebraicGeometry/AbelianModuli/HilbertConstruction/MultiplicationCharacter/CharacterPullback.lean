import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicationCharacter.Sheaves
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.SummandFunctoriality

/-! # Character Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The actual multiplication-character summands commute with arbitrary scheme pullback as split images of their pulled-back projectors. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {g N : ℕ} [NeZero N]
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (level : A.FullLevel N)

def Abelian.Schemes.AbelianScheme.multiplicationCharacterPullbackIso {Y : Scheme.{u}} (f : Y ⟶ A.scheme.left)
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0) :
    (Scheme.Modules.pullback f).obj (A.multiplicationCharacterSheaf level χ) ≅
      IdempotentSheafSummands.idempotentSheafSummand ((Scheme.Modules.pullback f).map
        (A.fullLevelMultiplicationProjector (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom) level χ)) :=
  Sheaf.SummandFunctoriality.sheafSummandPullbackIso f _
    (A.fullLevelMultiplicationProjector_idempotent (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom) level χ hN)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
