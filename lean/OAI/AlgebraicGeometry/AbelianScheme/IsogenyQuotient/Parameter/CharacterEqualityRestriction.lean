import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterEqualityOpen
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.OpenLineClassPullback

/-! # Character Equality Restriction -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterEqualityRestriction.Construction

noncomputable section

/-! Any parameter map into the constructed equality open identifies
the original line with its actual parameterized Cartier character line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  [IsProper B.hom] (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
  (hL : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left)
  (Q : Over S) (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

set_option backward.isDefEq.respectTransparency false in
theorem parameterCharacterEqualityOpen_restrict_class {P : Over S} (t : P ⟶ Q)
    (ht : ∀ x : P.left, t.left x ∈ CharacterEqualityOpen.Construction.parameterCharacterEqualityOpen f L hL Q χ) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst B.hom P.hom)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f P
        ((CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map t.op χ)) := by
  have hr : ∀ x : ((Over.pullback P.hom).obj B).left,
      CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B t x ∈ pullback.snd B.hom Q.hom ⁻¹ᵁ
        CharacterEqualityOpen.Construction.parameterCharacterEqualityOpen f L hL Q χ := by
    intro x
    change pullback.snd B.hom Q.hom (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B t x) ∈
      CharacterEqualityOpen.Construction.parameterCharacterEqualityOpen f L hL Q χ
    exact (congrArg (fun y => y ∈ CharacterEqualityOpen.Construction.parameterCharacterEqualityOpen f L hL Q χ)
      (congrArg (fun a => a x) (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_snd B t))).mpr
      (ht (pullback.snd B.hom P.hom x))
  have h := OpenLineClassPullback.Construction.lineClass_eq_pullback_of_range (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B t)
    (pullback.snd B.hom Q.hom ⁻¹ᵁ CharacterEqualityOpen.Construction.parameterCharacterEqualityOpen f L hL Q χ) hr
    (L.pullback (pullback.fst B.hom Q.hom)) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)
    (CharacterEqualityOpen.Construction.parameterCharacterEqualityOpen_class_eq f L hL Q χ)
  exact (LinePullbackKernel.Construction.originalLineParameter_class_natural L t).symm.trans
    (h.trans (Quotient.sound (CartierDuality.ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterLine_restrict f t χ)))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterEqualityRestriction.Construction
