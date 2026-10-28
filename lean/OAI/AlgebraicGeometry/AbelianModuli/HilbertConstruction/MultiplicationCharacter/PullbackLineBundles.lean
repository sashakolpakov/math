import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MultiplicationCharacter.PullbackIdentification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.CharacterLineBundles

/-! # Pullback Line Bundles -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Actual multiplication-character sheaves become line bundles after multiplication pullback, with frames transported from the proved constant-torsor character bundles. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} [NeZero N]
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (level : A.FullLevel N)

def Abelian.Schemes.AbelianScheme.multiplicationCharacterPullbackLineBundle
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0) :
    Line.Bundles.LineBundle A.scheme.left := by
  let G := ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))
  let c := Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom
  have hG := TameCharacters.fullLevelCharacter_order_nonzero K g N hN
  have := TameCharacters.tameFiniteAbelian_hasEnoughRoots K G hG
  let L := Constant.CharacterLineBundles.constantCharacterLineBundle c G χ hG
  let e : (Scheme.Modules.pullback (A.multiplication N).left).obj
      (A.multiplicationCharacterSheaf level χ) ≅ L.sheaf :=
    A.multiplicationCharacterComparisonIso level χ hN ≪≫
      eqToIso (Constant.CharacterLineBundles.constantCharacterLineBundle_sheaf c G χ hG).symm
  refine ⟨(Scheme.Modules.pullback (A.multiplication N).left).obj
    (A.multiplicationCharacterSheaf level χ), ?_⟩
  intro x
  obtain ⟨U, hx, ⟨frame⟩⟩ := L.locallyTrivial x
  exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso e ≪≫ frame⟩⟩

theorem Abelian.Schemes.AbelianScheme.multiplicationCharacterPullbackLineBundle_sheaf
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0) :
    (A.multiplicationCharacterPullbackLineBundle level χ hN).sheaf =
      (Scheme.Modules.pullback (A.multiplication N).left).obj
        (A.multiplicationCharacterSheaf level χ) := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
