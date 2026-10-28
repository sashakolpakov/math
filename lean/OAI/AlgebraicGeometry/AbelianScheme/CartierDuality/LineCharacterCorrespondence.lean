import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.EffectiveKernelCharacters

/-! # Line Character Correspondence -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterCorrespondence.Construction.KernelCharacters

noncomputable section

/-!
# CartierDuality: actual pullback-trivial line classes and kernel characters
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {k : Type u} [Field k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [IsAffine (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).left] [IsAffineHom f.left] [Flat f.left] [Surjective f.left]
    (C : CommHopfAlgCat k) (i : (hopfSpec (.of k)).obj (.op C) ≅ Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))

/-- The native Hopf presentation is also an isomorphism of the underlying schemes over the base. -/
def kernelPresentationUnderlyingIso : ((hopfSpec (.of k)).obj (.op C)).X ≅ Picard.Homomorphisms.Kernel.Construction.kernelScheme f where
  hom := i.hom.hom.hom
  inv := i.inv.hom.hom
  hom_inv_id := congrArg (fun a => a.hom.hom) i.hom_inv_id
  inv_hom_id := congrArg (fun a => a.hom.hom) i.inv_hom_id

/-- The inverse character construction is the class of the actual descended global line. -/
def lineClassOfKernelCharacter (z : GroupLike k C) :
    {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.left // AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left} :=
  EffectiveKernelCharacters.Construction.KernelCharacters.characterPullbackKernelClass f (KernelCharacterGluing.Construction.KernelCharacters.hopfKernelUnitHom f i z) (KernelCharacterGluing.Construction.KernelCharacters.hopfKernelUnitHom_natural f i z)

/-- The actual character attached to the constructed line is the supplied character. -/
theorem lineClassOfKernelCharacter_character (z : GroupLike k C) :
    LineCharacterIndependence.Construction.KernelCharacters.pullbackClassCharacter f C i.hom.hom.hom (lineClassOfKernelCharacter f C i z) = z := by
  have hc := LineCharacterIndependence.Construction.KernelCharacters.pullbackClassCharacter_eq f C i.hom.hom.hom (lineClassOfKernelCharacter f C i z)
    (EffectiveKernelCharacters.Construction.KernelCharacters.hopfCharacterDescendedLine f i z) rfl (EffectiveKernelCharacters.Construction.KernelCharacters.hopfCharacterDescendedLineFrame f i z)
  apply hc.trans
  apply GroupLike.ext
  exact EffectiveKernelCharacters.Construction.KernelCharacters.hopfCharacterDescendedLine_coordinate f i z

/-- Every actual kernel character is realized by an actual pullback-trivial line bundle. -/
theorem pullbackClassCharacter_surjective : Function.Surjective (LineCharacterIndependence.Construction.KernelCharacters.pullbackClassCharacter f C i.hom.hom.hom) :=
  fun z => ⟨lineClassOfKernelCharacter f C i z, lineClassOfKernelCharacter_character f C i z⟩

/-- The line-character correspondence has effective global descent as its inverse. -/
def pullbackClassCharacterEquiv :
    {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.left // AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left} ≃
      GroupLike k C where
  toFun := LineCharacterIndependence.Construction.KernelCharacters.pullbackClassCharacter f C i.hom.hom.hom
  invFun := lineClassOfKernelCharacter f C i
  left_inv q := by
    have : IsMonHom (kernelPresentationUnderlyingIso f C i).hom :=
      inferInstanceAs (IsMonHom i.hom.hom.hom)
    exact LineCharacterIndependence.Construction.KernelCharacters.pullbackClassCharacter_injective f C (kernelPresentationUnderlyingIso f C i)
      (lineClassOfKernelCharacter_character f C i (LineCharacterIndependence.Construction.KernelCharacters.pullbackClassCharacter f C i.hom.hom.hom q))
  right_inv := lineClassOfKernelCharacter_character f C i

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterCorrespondence.Construction.KernelCharacters
