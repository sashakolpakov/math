import OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.CharacterEvaluation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CartierTorsionRepresentative

/-! # Torsion Character -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TorsionCharacter

noncomputable section

/-! Construct the character of a prescribed dual torsion point and compute its actual Poincare gluing. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Homomorphisms.GroupDescent.Construction.groupHom_pow_isMonHom

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A.scheme)
  (ell : A.scheme ⟶ D.withPicardGroup.abelian) [IsMonHom ell]
  [IsFinite ell.left] [Flat ell.left] [Surjective ell.left]
  (n : ℕ) (hn : 0 < n)
  [IsFinite ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [Flat ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [Surjective ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  [LocallyOfFinitePresentation ((𝟙 A.scheme : A.scheme ⟶ A.scheme) ^ n).left]
  (C : AbelianScheme.CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n))))
  (T : Over (Spec (.of k))) (y : T ⟶ D.withPicardGroup.abelian) (hy : y ^ n = 1)

/-- The character is constructed by the actual inverse Cartier-Picard isomorphism. -/
def character : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)))).obj.obj (.op T) :=
  C.sectionEquiv T (CartierTorsionRepresentative.representative A.scheme D ell n hn C y hy)

omit [IsAlgClosed k] in
/-- This actual character represents the specified dual point. -/
theorem character_point :
    AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint ((𝟙 A.scheme) ^ n) T (character A D ell n hn C T y hy) D.withPicardGroup = y :=
  CartierTorsionRepresentative.representative_point A.scheme D ell n hn C y hy

variable [IsAffine T.left]
  (s : (Scheme.Modules.pullback (𝟙 T ⊗ₘ (𝟙 A.scheme) ^ n).left).obj
    (PointNormalization.line D.withPicardGroup y).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (T ⊗ A.scheme).left)

/-- The prescribed torsion point's actual Poincare line has its constructed Cartier character on all translations. -/
theorem scalar_translation {U : Over (Spec (.of k))} (a : U ⟶ T) (x : U ⟶ A.scheme)
    (b : U ⟶ Homomorphisms.Kernel.Construction.kernelScheme ((𝟙 A.scheme) ^ n)) (q : U ⟶ T ⊗ A.scheme)
    (hx : lift a x ≫ (𝟙 T ⊗ₘ (𝟙 A.scheme) ^ n) = q)
    (hb : lift a (x * (b ≫ Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.scheme) ^ n))) ≫ (𝟙 T ⊗ₘ (𝟙 A.scheme) ^ n) = q) :
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar
      (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (𝟙 T ⊗ₘ (𝟙 A.scheme) ^ n).left
        (PointNormalization.line D.withPicardGroup y).sheaf) s
      q.left (lift a x).left (lift a (x * (b ≫ Homomorphisms.Kernel.Construction.kernelInclusion ((𝟙 A.scheme) ^ n)))).left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hb) =
    (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom U
      ((character A D ell n hn C T y hy).app (.op (Over.mk a)) b)).val :=
  CharacterEvaluation.Prescribed.scalar_translation A D.withPicardGroup ((𝟙 A.scheme) ^ n) T
    (character A D ell n hn C T y hy) y (character_point A D ell n hn C T y hy) s a x b q hx hb

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.TorsionCharacter
