import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Multiplication.StructureBaseChangeIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicationCharacter.Comparison

/-! # Pullback Identification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Each pulled-back multiplication-character sheaf is canonically isomorphic to the actual corresponding character sheaf on the constant torsor. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {g N : ℕ} [NeZero N]
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (level : A.FullLevel N)

def Abelian.Schemes.AbelianScheme.multiplicationCharacterComparisonIso
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0) :
    (Scheme.Modules.pullback (A.multiplication N).left).obj
        (A.multiplicationCharacterSheaf level χ) ≅
      Constant.CharacterSheafSections.constantCharacterSheaf (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom)
        (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) χ :=
  A.multiplicationCharacterPullbackIso level (A.multiplication N).left χ hN ≪≫
    Sheaf.SummandIntertwining.sheafSummandIntertwiningIso _ _ (A.fullLevelStructureComparisonIso level)
      (A.fullLevelStructureComparison_projector level χ)

theorem Abelian.Schemes.AbelianScheme.multiplicationCharacterComparisonIso_hom
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0) :
    (A.multiplicationCharacterComparisonIso level χ hN).hom =
      A.multiplicationCharacterComparison level χ hN := rfl

theorem Abelian.Schemes.AbelianScheme.multiplicationCharacterComparison_isIso
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0) :
    IsIso (A.multiplicationCharacterComparison level χ hN) := by
  rw [← A.multiplicationCharacterComparisonIso_hom level χ hN]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
