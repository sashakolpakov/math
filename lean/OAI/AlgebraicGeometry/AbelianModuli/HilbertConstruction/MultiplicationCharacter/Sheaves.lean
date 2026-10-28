import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LevelMultiplication.Projectors
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Sheaf.CharacterEigenmaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrthogonalSheafDecomposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf

/-! # Sheaves -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Over the coefficient field, the multiplication pushforward decomposes into actual character sheaves. Its translations, coefficient map, projections, and splitting maps are all constructed. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {g N : ℕ} [NeZero N]
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of K))) (level : A.FullLevel N)

def Abelian.Schemes.AbelianScheme.multiplicationCharacterSheaf
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) : A.scheme.left.Modules :=
  IdempotentSheafSummands.idempotentSheafSummand
    (A.fullLevelMultiplicationProjector (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom) level χ)

def Abelian.Schemes.AbelianScheme.multiplicationCharacterInclusion
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) :
    A.multiplicationCharacterSheaf level χ ⟶ A.multiplicationStructurePushforward N :=
  IdempotentSheafSummands.idempotentSheafInclusion
    (A.fullLevelMultiplicationProjector (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom) level χ)

def Abelian.Schemes.AbelianScheme.multiplicationCharacterRetraction
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0) :
    A.multiplicationStructurePushforward N ⟶ A.multiplicationCharacterSheaf level χ :=
  IdempotentSheafSummands.idempotentSheafRetraction _
    (A.fullLevelMultiplicationProjector_idempotent (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom) level χ hN)

theorem Abelian.Schemes.AbelianScheme.multiplicationCharacterInclusion_retraction
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) (hN : (N : K) ≠ 0) :
    A.multiplicationCharacterInclusion level χ ≫ A.multiplicationCharacterRetraction level χ hN =
      𝟙 (A.multiplicationCharacterSheaf level χ) :=
  IdempotentSheafSummands.idempotentSheafInclusion_retraction _ _

theorem Abelian.Schemes.AbelianScheme.multiplicationCharacterSheaf_eigen
    (χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ)
    (a : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N))) :
    A.multiplicationCharacterInclusion level χ ≫ A.fullLevelStructureRepresentation level a =
      Global.ModuleScalars.globalModuleScalar (A.multiplicationCharacterSheaf level χ)
        (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom (χ a : K)) ≫ A.multiplicationCharacterInclusion level χ :=
  Sheaf.CharacterEigenmaps.sheafCharacterSummand_eigen _ _ _ χ a

def Abelian.Schemes.AbelianScheme.multiplicationCharacterDecomposition [IsAlgClosed K] (hN : (N : K) ≠ 0) :
    A.multiplicationStructurePushforward N ≅
      ⨁ (fun χ : ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ =>
        A.multiplicationCharacterSheaf level χ) := by
  classical
  letI : Fintype (ULift.{u} (Multiplicative (Fin (2 * g) → ZMod N)) →* Kˣ) := Fintype.ofFinite _
  exact OrthogonalSheafDecomposition.orthogonalIdempotentSheafIso _
    (fun χ => A.fullLevelMultiplicationProjector_idempotent
      (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom) level χ hN)
    (fun χ ψ h => A.fullLevelMultiplicationProjector_orthogonal
      (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom) level ψ χ hN h)
    (A.fullLevelMultiplicationProjector_sum (Coefficient.ModulePresheaf.schemeCoefficientMap A.scheme.hom) level hN)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
