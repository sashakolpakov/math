import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyCartierRecoveryOpen
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.FlatKernelCartierRepresentation

/-! # Family Character Line Cover -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyCharacterLineCover.Construction

noncomputable section

/-! Every actual pullback-trivial parameter line is a character line
on an etale surjective cover of that parameter. Characters belong to
the original relative kernel, without changing Cartier representatives. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
  (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (T : Over S) (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((Over.pullback T.hom).obj B).left)
  (hL : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback T.hom).map f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.pullback T.hom).obj A).left)

include hL

def familyCharacterCoverParameter
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))) : Over S :=
  Over.mk ((FamilyCartierRecoveryOpen.Construction.familyCartierRecoveryOpen f T L hL C).ι ≫ (T ⊗ C.dual.X).hom)

def familyCharacterCoverLift
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))) :
    familyCharacterCoverParameter f T L hL C ⟶ T ⊗ C.dual.X :=
  Over.homMk (FamilyCartierRecoveryOpen.Construction.familyCartierRecoveryOpen f T L hL C).ι rfl

def familyCharacterCoverMap
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))) :
    familyCharacterCoverParameter f T L hL C ⟶ T :=
  familyCharacterCoverLift f T L hL C ≫ fst T C.dual.X

def familyCharacterCoverCharacter
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))) :
    (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op (familyCharacterCoverParameter f T L hL C)) :=
  (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.map (familyCharacterCoverLift f T L hL C).op
    (C.sectionEquiv (T ⊗ C.dual.X) (snd T C.dual.X))

omit [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [GeometricallyConnected B.hom] in
set_option backward.isDefEq.respectTransparency false in
theorem familyCharacterCover_class
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B (familyCharacterCoverMap f T L hL C))) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f (familyCharacterCoverParameter f T L hL C)
        (familyCharacterCoverCharacter f T L hL C)) := by
  apply FamilyCartierRecoveryOpen.Construction.familyCartierRecoveryOpen_restrict_class f T L hL C (familyCharacterCoverLift f T L hL C)
  intro x
  exact x.property

omit [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
    [Smooth B.hom] [GeometricallyConnected B.hom] in
theorem familyCharacterCoverMap_etale
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    Etale (familyCharacterCoverMap f T L hL C).left :=
  FamilyCartierRecoveryOpen.Construction.familyCartierRecoveryOpen_etale f T L hL C p n hn hk

theorem familyCharacterCoverMap_surjective
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k)) :
    Surjective (familyCharacterCoverMap f T L hL C).left :=
  FamilyCartierRecoveryOpen.Construction.familyCartierRecoveryOpen_surjective f T L hL C p

set_option backward.isDefEq.respectTransparency false in
theorem exists_familyCharacterLine_cover
    (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    ∃ (P : Over S) (a : P ⟶ T), Etale a.left ∧ Surjective a.left ∧
      ∃ χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op P),
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B a)) =
          AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f P χ) :=
  ⟨familyCharacterCoverParameter f T L hL C, familyCharacterCoverMap f T L hL C,
    familyCharacterCoverMap_etale f T L hL C p n hn hk,
    familyCharacterCoverMap_surjective f T L hL C p,
    familyCharacterCoverCharacter f T L hL C, familyCharacterCover_class f T L hL C⟩

theorem exists_canonicalFamilyCharacterLine_cover [IsCommMonObj A]
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    ∃ (P : Over S) (a : P ⟶ T), Etale a.left ∧ Surjective a.left ∧
      ∃ χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op P),
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterPullbackMap B a)) =
          AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f P χ) :=
  exists_familyCharacterLine_cover f T L hL (Finite.FlatKernelCartierRepresentation.Construction.finiteFlatKernelCartierRepresentation f) p n hn hk

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyCharacterLineCover.Construction
