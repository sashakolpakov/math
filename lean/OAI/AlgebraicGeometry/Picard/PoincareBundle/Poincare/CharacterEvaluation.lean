import OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterScalars
import OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterFamilyEvaluation

/-! # Character Evaluation -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.CharacterEvaluation

noncomputable section

section

/-! The Poincare line of an actual Cartier-Picard character evaluates that character on every kernel translation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A.scheme)
  {X : Over (Spec (.of k))} [GrpObj X] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  (f : X ⟶ A.scheme) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (T : Over (Spec (.of k))) [IsAffine T.left]
  (χ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op T))
  (s : (Scheme.Modules.pullback (𝟙 T ⊗ₘ f).left).obj
    (PointNormalization.line D (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T χ D)).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (T ⊗ X).left)

/-- Every actual global pullback frame of this Poincare line gives precisely the represented character. -/
theorem scalar_translation {U : Over (Spec (.of k))} (a : U ⟶ T) (x : U ⟶ X)
    (b : U ⟶ Homomorphisms.Kernel.Construction.kernelScheme f) (q : U ⟶ T ⊗ A.scheme)
    (hx : lift a x ≫ (𝟙 T ⊗ₘ f) = q)
    (hy : lift a (x * (b ≫ Homomorphisms.Kernel.Construction.kernelInclusion f)) ≫ (𝟙 T ⊗ₘ f) = q) :
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar
      (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (𝟙 T ⊗ₘ f).left
        (PointNormalization.line D (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T χ D)).sheaf) s
      q.left (lift a x).left (lift a (x * (b ≫ Homomorphisms.Kernel.Construction.kernelInclusion f))).left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hy) =
    (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom U (χ.app (.op (Over.mk a)) b)).val :=
  (CharacterScalars.Poincare.scalar_eq A D f T χ s q (lift a x)
    (lift a (x * (b ≫ Homomorphisms.Kernel.Construction.kernelInclusion f))) hx hy).trans
      (CharacterFamilyEvaluation.Family.scalar_translation f T χ a x b q hx hy)

end

/-! The character calculation is expressed at a prescribed actual dual point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace Prescribed

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A.scheme)
  {X : Over (Spec (.of k))} [GrpObj X] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  (f : X ⟶ A.scheme) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (T : Over (Spec (.of k))) [IsAffine T.left]
  (χ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op T))
  (y : T ⟶ D.abelian) (hy : AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T χ D = y)
  (s : (Scheme.Modules.pullback (𝟙 T ⊗ₘ f).left).obj
    (PointNormalization.line D y).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (T ⊗ X).left)

include hy

/-- Equality of represented dual points suffices for the actual scalar formula. -/
theorem scalar_translation {U : Over (Spec (.of k))} (a : U ⟶ T) (x : U ⟶ X)
    (b : U ⟶ Homomorphisms.Kernel.Construction.kernelScheme f) (q : U ⟶ T ⊗ A.scheme)
    (hx : lift a x ≫ (𝟙 T ⊗ₘ f) = q)
    (hb : lift a (x * (b ≫ Homomorphisms.Kernel.Construction.kernelInclusion f)) ≫ (𝟙 T ⊗ₘ f) = q) :
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar
      (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (𝟙 T ⊗ₘ f).left (PointNormalization.line D y).sheaf) s
      q.left (lift a x).left (lift a (x * (b ≫ Homomorphisms.Kernel.Construction.kernelInclusion f))).left
      (congrArg Over.Hom.left hx) (congrArg Over.Hom.left hb) =
    (AbelianScheme.CartierDuality.CharacterUnitValues.Construction.Schemes.multiplicativeGroupUnitHom U (χ.app (.op (Over.mk a)) b)).val := by
  subst y
  exact CharacterEvaluation.scalar_translation A D f T χ s a x b q hx hb

end Prescribed

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Poincare.CharacterEvaluation
