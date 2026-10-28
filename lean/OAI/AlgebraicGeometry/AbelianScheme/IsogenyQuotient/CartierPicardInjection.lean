import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardHomomorphism
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterLineFaithfulness
import OAI.AlgebraicGeometry.Picard.Homomorphisms.GeometricSheafification

/-! # Cartier Picard Injection -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierPicardInjection.Construction

noncomputable section

/-!
The actual Cartier-to-Picard map constructed by line descent is
injective on geometric points. Equality is detected by the original
Poincare classes and the actual character lines, without assuming a
perfect ambient pairing or a torsion-duality isomorphism.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.GeometricSheafification.Construction

universe u

theorem cartierToPicard_geometric_injective
    {k : Type u} [Field k] [IsAlgClosed k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    (f : A ⟶ B) [IsMonHom f]
    [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))) :
    Function.Injective (fun x : Over.mk (𝟙 (Spec (.of k))) ⟶ C.dual.X => x ≫ CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C) := by
  let T : Over (Spec (.of k)) := Over.mk (𝟙 (Spec (.of k)))
  let : IsAffine T.left := inferInstanceAs (IsAffine (Spec (.of k)))
  have : IsIso ((Over.pullback T.hom).obj A).hom.appTop := CartierDuality.CharacterLineFaithfulness.Construction.KernelCharacters.properGroup_parameter_appTop_isIso A T
  have hp := (ConcreteCategory.bijective_of_isIso ((Over.pullback T.hom).obj A).hom.appTop).surjective
  intro x y hxy
  apply (C.sectionEquiv T).injective
  apply CartierDuality.CharacterLineFaithfulness.Construction.KernelCharacters.parameterLineClass_injective f T hp
  apply (Picard.Homomorphisms.GeometricSheafification.Construction.toSheafify_algClosed_bijective k (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.relativePicardPresheaf B)).injective
  have hpoints : CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T (C.sectionEquiv T x) D =
      CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T (C.sectionEquiv T y) D :=
    (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply f D C T x).symm.trans (hxy.trans (CartierDuality.PicardHomomorphism.Construction.KernelCharacters.cartierToPicard_apply f D C T y))
  exact (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint_poincare f T (C.sectionEquiv T x) D).symm.trans
    ((congrArg (Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard.poincareClass D) hpoints).trans
      (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint_poincare f T (C.sectionEquiv T y) D))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierPicardInjection.Construction
