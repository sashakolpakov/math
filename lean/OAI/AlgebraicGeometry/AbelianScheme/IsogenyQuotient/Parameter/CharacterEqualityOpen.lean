import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.LinePullbackKernel
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.LineEqualityBaseChange

/-! # Character Equality Open -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterEqualityOpen.Construction

noncomputable section

/-! A parameterized character line agrees with an original
pullback-trivial line on a constructed open of its parameter scheme.
Every characteristic-zero field parameter where they agree lies in it. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  [IsProper B.hom] (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle B.left)
  (hL : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left)
  (Q : Over S) (χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q))

include hL

omit [IsProper B.hom] [LocallyOfFinitePresentation f.left] in
theorem parameterCharacterEquality_pullback :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst B.hom Q.hom))) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) :=
  (LinePullbackKernel.Construction.originalLineParameter_pullback_trivial f L hL Q).trans
    (LinePullbackKernel.Construction.parameterCharacterLine_actual_pullback_trivial f Q χ).symm

def parameterCharacterEqualityOpen : Q.left.Opens := by
  have : IsProper ((Over.pullback Q.hom).obj B).hom :=
    inferInstanceAs (IsProper (pullback.snd B.hom Q.hom))
  have : IsFinite ((Over.pullback Q.hom).map f).left :=
    MorphismProperty.overPullbackMap (P := @IsFinite) Q.hom _ inferInstance
  have : Flat ((Over.pullback Q.hom).map f).left :=
    MorphismProperty.overPullbackMap (P := @Flat) Q.hom _ inferInstance
  have : LocallyOfFinitePresentation ((Over.pullback Q.hom).map f).left :=
    MorphismProperty.overPullbackMap (P := @LocallyOfFinitePresentation) Q.hom _ inferInstance
  exact Relative.LineEqualityOpen.Construction.lineEqualityOpen ((Over.pullback Q.hom).map f)
    (L.pullback (pullback.fst B.hom Q.hom)) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)
    (parameterCharacterEquality_pullback f L hL Q χ)

set_option backward.isDefEq.respectTransparency false in
theorem parameterCharacterEqualityOpen_class_eq :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      (pullback.snd B.hom Q.hom ⁻¹ᵁ parameterCharacterEqualityOpen f L hL Q χ).ι
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst B.hom Q.hom))) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass
      (pullback.snd B.hom Q.hom ⁻¹ᵁ parameterCharacterEqualityOpen f L hL Q χ).ι
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
    (L.pullback (pullback.fst B.hom Q.hom)) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)
    (parameterCharacterEquality_pullback f L hL Q χ)

set_option backward.isDefEq.respectTransparency false in
theorem parameterCharacterEqualityOpen_contains_field_character
    [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [GeometricallyConnected B.hom]
    {k : Type u} [Field k] [CharZero k] (t : Spec (.of k) ⟶ S)
    (d : Over.mk t ⟶ Q)
    (hχ : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f (Over.mk t)
      ((CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map d.op χ)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (pullback.fst B.hom t)))
    (s : Spec (.of k)) : d.left s ∈ parameterCharacterEqualityOpen f L hL Q χ := by
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
    (L.pullback (pullback.fst B.hom Q.hom)) (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)
    (parameterCharacterEquality_pullback f L hL Q χ) d.left
    (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B d) (pullback.snd B.hom t) (PullbackSquare.Construction.parameterPullbackMap_isPullback B d) _ s
  exact (LinePullbackKernel.Construction.originalLineParameter_class_natural L d).trans
    (hχ.symm.trans (Quotient.sound (CartierDuality.ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterLine_restrict f d χ)).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.CharacterEqualityOpen.Construction
