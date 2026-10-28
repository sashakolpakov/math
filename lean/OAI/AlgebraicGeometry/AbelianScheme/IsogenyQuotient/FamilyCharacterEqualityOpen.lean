import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.LineComposition
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterEqualityRestriction

/-! # Family Character Equality Open -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyCharacterEqualityOpen.Construction

noncomputable section

/-! Equality with a Cartier character line is constructed for an
arbitrary line on an arbitrary parameter family, using the original
kernel and character sheaf throughout. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  [IsProper B.hom] (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (T : Over S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback T.hom).obj B).left)
  (hL : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback T.hom).map f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.pullback T.hom).obj A).left)
  {Q : Over S} (a : Q ⟶ T)
  (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

include hL

omit [IsProper B.hom] [LocallyOfFinitePresentation f.left] in
theorem familyCharacterEquality_pullback :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B a))) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) :=
  (Parameter.LineComposition.Construction.parameterFamilyLine_pullback_trivial B f a L hL).trans
    (Parameter.LinePullbackKernel.Construction.parameterCharacterLine_actual_pullback_trivial f Q χ).symm

def familyCharacterEqualityOpen : Q.left.Opens := by
  have : IsProper ((Over.pullback Q.hom).obj B).hom :=
    inferInstanceAs (IsProper (pullback.snd B.hom Q.hom))
  have : IsFinite ((Over.pullback Q.hom).map f).left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) Q.hom _ inferInstance
  have : Flat ((Over.pullback Q.hom).map f).left :=
    MorphismProperty.overPullbackMap (P := @Flat) Q.hom _ inferInstance
  have : LocallyOfFinitePresentation ((Over.pullback Q.hom).map f).left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) Q.hom _ inferInstance
  exact Relative.LineEqualityOpen.Construction.lineEqualityOpen ((Over.pullback Q.hom).map f)
    (L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B a)) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)
    (familyCharacterEquality_pullback f T L hL a χ)

set_option backward.isDefEq.respectTransparency false in
theorem familyCharacterEqualityOpen_class_eq :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      (pullback.snd B.hom Q.hom ⁻¹ᵁ familyCharacterEqualityOpen f T L hL a χ).ι
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B a))) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      (pullback.snd B.hom Q.hom ⁻¹ᵁ familyCharacterEqualityOpen f T L hL a χ).ι
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) := by
  have : IsProper ((Over.pullback Q.hom).obj B).hom :=
    inferInstanceAs (IsProper (pullback.snd B.hom Q.hom))
  have : IsFinite ((Over.pullback Q.hom).map f).left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) Q.hom _ inferInstance
  have : Flat ((Over.pullback Q.hom).map f).left :=
    MorphismProperty.overPullbackMap (P := @Flat) Q.hom _ inferInstance
  have : LocallyOfFinitePresentation ((Over.pullback Q.hom).map f).left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) Q.hom _ inferInstance
  exact Relative.LineEqualityOpen.Construction.lineEqualityOpen_class_eq ((Over.pullback Q.hom).map f)
    (L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B a)) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)
    (familyCharacterEquality_pullback f T L hL a χ)

set_option backward.isDefEq.respectTransparency false in
theorem familyCharacterEqualityOpen_contains_field_character
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [GeometricallyConnected B.hom]
    {k : Type u} [Field k] [CharZero k] (t : Spec (.of k) ⟶ S)
    (d : Over.mk t ⟶ Q)
    (hχ : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f (Over.mk t)
      ((CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map d.op χ)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B (d ≫ a))))
    (s : Spec (.of k)) : d.left s ∈ familyCharacterEqualityOpen f T L hL a χ := by
  let A' := (Over.pullback Q.hom).obj A
  let B' := (Over.pullback Q.hom).obj B
  let f' := (Over.pullback Q.hom).map f
  have : IsProper A'.hom := inferInstanceAs (IsProper (pullback.snd A.hom Q.hom))
  have : Smooth A'.hom := inferInstanceAs (Smooth (pullback.snd A.hom Q.hom))
  have : GeometricallyConnected A'.hom := inferInstanceAs (GeometricallyConnected (pullback.snd A.hom Q.hom))
  have : IsProper B'.hom := inferInstanceAs (IsProper (pullback.snd B.hom Q.hom))
  have : Smooth B'.hom := inferInstanceAs (Smooth (pullback.snd B.hom Q.hom))
  have : GeometricallyConnected B'.hom := inferInstanceAs (GeometricallyConnected (pullback.snd B.hom Q.hom))
  have : IsFinite f'.left := MorphismProperty.overPullbackMap (P := @IsFinite) Q.hom _ inferInstance
  have : Flat f'.left := MorphismProperty.overPullbackMap (P := @Flat) Q.hom _ inferInstance
  have : Surjective f'.left := MorphismProperty.overPullbackMap (P := @Surjective) Q.hom _ inferInstance
  have : LocallyOfFinitePresentation f'.left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) Q.hom _ inferInstance
  apply LineEqualityBaseChange.Construction.lineEqualityOpen_contains_field_isPullback f'
    (L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B a)) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)
    (familyCharacterEquality_pullback f T L hL a χ) d.left
    (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B d) (pullback.snd B.hom t) (Parameter.PullbackSquare.Construction.parameterPullbackMap_isPullback B d) _ s
  exact (Parameter.LineComposition.Construction.parameterFamilyLine_class_natural B L d a).trans
    (hχ.symm.trans (Quotient.sound (CartierDuality.ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterLine_restrict f d χ)).symm)

set_option backward.isDefEq.respectTransparency false in
theorem familyCharacterEqualityOpen_restrict_class {P : Over S} (b : P ⟶ Q)
    (hb : ∀ x : P.left, b.left x ∈ familyCharacterEqualityOpen f T L hL a χ) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B (b ≫ a))) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f P
        ((CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map b.op χ)) := by
  have hr : ∀ x : ((Over.pullback P.hom).obj B).left,
      CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B b x ∈ pullback.snd B.hom Q.hom ⁻¹ᵁ
        familyCharacterEqualityOpen f T L hL a χ := by
    intro x
    change pullback.snd B.hom Q.hom (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B b x) ∈
      familyCharacterEqualityOpen f T L hL a χ
    exact (congrArg (fun y => y ∈ familyCharacterEqualityOpen f T L hL a χ)
      (congrArg (fun m => m x) (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap_snd B b))).mpr
      (hb (pullback.snd B.hom P.hom x))
  have h := OpenLineClassPullback.Construction.lineClass_eq_pullback_of_range (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B b)
    (pullback.snd B.hom Q.hom ⁻¹ᵁ familyCharacterEqualityOpen f T L hL a χ) hr
    (L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B a)) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)
    (familyCharacterEqualityOpen_class_eq f T L hL a χ)
  exact (Parameter.LineComposition.Construction.parameterFamilyLine_class_natural B L b a).symm.trans
    (h.trans (Quotient.sound (CartierDuality.ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterLine_restrict f b χ)))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyCharacterEqualityOpen.Construction
