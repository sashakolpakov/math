import OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterComparison
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterIndependence
import OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Vertical.KernelDescent

/-! # Character Scalars -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterScalars

noncomputable section

/-! The normalized Poincare family and its actual CartierDuality character line have identical native gluing scalars. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace Poincare

open OAI.AlgebraicGeometry.Picard.Homomorphisms.ProperGroupFunctions.Construction OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterIndependence.Construction.KernelCharacters

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))) (D : Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A.scheme)
  {X : Over (Spec (.of k))} [GrpObj X] [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  (f : X ⟶ A.scheme) [IsMonHom f]
  [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (T : Over (Spec (.of k))) [IsAffine T.left]
  (χ : (AbelianScheme.CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op T))
  (s : (Scheme.Modules.pullback (𝟙 T ⊗ₘ f).left).obj
    (Poincare.PointNormalization.line D (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T χ D)).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (T ⊗ X).left)

/-- The actual scalar of the Poincare line is the actual scalar of its character-descended line. -/
theorem scalar_eq {U : Over (Spec (.of k))} (q : U ⟶ T ⊗ A.scheme) (a b : U ⟶ T ⊗ X)
    (ha : a ≫ (𝟙 T ⊗ₘ f) = q) (hb : b ≫ (𝟙 T ⊗ₘ f) = q) :
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar
      (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (𝟙 T ⊗ₘ f).left
        (Poincare.PointNormalization.line D (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T χ D)).sheaf) s
      q.left a.left b.left (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hb) =
    Homomorphisms.FramedDescentScalars.Construction.framedDescentScalar (Homomorphisms.CanonicalDescentFrames.Construction.canonicalModuleDescent (𝟙 T ⊗ₘ f).left (CharacterFamilyLine.Family.line f T χ).sheaf)
      (CharacterFamilyFrames.Family.pullbackFrame f T χ) q.left a.left b.left
      (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hb) := by
  obtain ⟨e, _he⟩ := CharacterComparison.Poincare.exists_normalized_iso A D f T χ
  have : IsIso (fst T X).left.appTop := Homomorphisms.ProperGroupFunctions.Construction.properGroupProduct_appTop_isIso X T
  exact AbelianScheme.CartierDuality.LineCharacterIndependence.Construction.KernelCharacters.canonicalScalar_eq_of_lineIso (fst T X).left
    (ConcreteCategory.bijective_of_isIso (fst T X).left.appTop).surjective (𝟙 T ⊗ₘ f).left
    (Poincare.PointNormalization.line D (AbelianScheme.CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T χ D))
    (CharacterFamilyLine.Family.line f T χ) e s (CharacterFamilyFrames.Family.pullbackFrame f T χ)
    q.left a.left b.left (congrArg Over.Hom.left ha) (congrArg Over.Hom.left hb)
    (congrArg Over.Hom.left (Vertical.KernelDescent.relation f a b (ha.trans hb.symm)).2)

end Poincare

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.CharacterScalars
