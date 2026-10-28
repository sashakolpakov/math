import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.ParameterLineNaturality
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.CharacterTorsionFactor

/-! # Picard Homomorphism -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardHomomorphism

noncomputable section

/-!
# CartierDuality: the actual Cartier-to-Picard torsion morphism is a group homomorphism
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

universe u

namespace Construction.CharacterEvaluation

/-- Evaluate a pointwise Yoneda construction before instantiating its geometric point formulas. -/
theorem pointTransformation_preimage_id {V : Type*} [Category* V] [CartesianMonoidalCategory V]
    {G H : Grp V} (p : ∀ T : V, (T ⟶ G.X) →* (T ⟶ H.X))
    (hp : ∀ {T U : V} (t : U ⟶ T) (x : T ⟶ G.X), p U (t ≫ x) = t ≫ p T x) :
    (yonedaGrpFullyFaithful.preimage (Evaluation.Construction.CharacterEvaluation.pointTransformation p hp)).hom.hom = p G.X (𝟙 G.X) := by
  have h : (𝟙 G.X) ≫ (yonedaGrpFullyFaithful.preimage (Evaluation.Construction.CharacterEvaluation.pointTransformation p hp)).hom.hom = p G.X (𝟙 G.X) :=
    Evaluation.Construction.CharacterEvaluation.yonedaGrp_preimage_points (Evaluation.Construction.CharacterEvaluation.pointTransformation p hp) G.X (𝟙 G.X)
  exact (Category.id_comp _).symm.trans h

end Construction.CharacterEvaluation

namespace Construction.KernelCharacters

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f]
    [IsAffineHom f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
    (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData B) (C : GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))

/-- The native universal morphism acts by character-line descent on every test scheme. -/
theorem cartierToPicard_apply (T : Over S) (x : T ⟶ C.dual.X) :
    x ≫ ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C = ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T (C.sectionEquiv T x) D := by
  have hn := ParameterLineNaturality.Construction.KernelCharacters.parameterCharacterDualPoint_natural f x (C.sectionEquiv C.dual.X (𝟙 C.dual.X)) D
  have hc := C.sectionEquiv_natural x (𝟙 C.dual.X)
  rw [Category.comp_id] at hc
  exact hn.trans (congrArg (fun χ => ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterDualPoint f T χ D) hc.symm)

/-- The point homomorphisms of the actual universal morphism. -/
def cartierToPicardPoints (T : Over S) :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    (T ⟶ C.dual.X) →* (T ⟶ D.abelian) :=
  letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  (ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterDualPointHom f T D).comp (C.sectionEquiv T).toMonoidHom

theorem cartierToPicardPoints_apply (T : Over S) (x : T ⟶ C.dual.X) :
    cartierToPicardPoints f D C T x = x ≫ ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C :=
  (cartierToPicard_apply f D C T x).symm

/-- The point homomorphisms agree under every test-scheme restriction. -/
theorem cartierToPicardPoints_natural {T U : Over S} (t : U ⟶ T) (x : T ⟶ C.dual.X) :
    cartierToPicardPoints f D C U (t ≫ x) = t ≫ cartierToPicardPoints f D C T x := by
  rw [cartierToPicardPoints_apply, cartierToPicardPoints_apply, Category.assoc]

/-- Yoneda bundles the actual character-line construction as a morphism of native group schemes. -/
def cartierToPicardGroup :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    C.dual ⟶ Grp.mk D.abelian :=
  letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  yonedaGrpFullyFaithful.preimage
    (Evaluation.Construction.CharacterEvaluation.pointTransformation (G := C.dual) (H := Grp.mk D.abelian) (cartierToPicardPoints f D C)
      (cartierToPicardPoints_natural f D C))

/-- The bundled homomorphism retains the original actual character-line morphism. -/
theorem cartierToPicardGroup_underlying : (cartierToPicardGroup f D C).hom.hom = ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  have h := CharacterEvaluation.pointTransformation_preimage_id (G := C.dual) (H := Grp.mk D.abelian)
    (cartierToPicardPoints f D C) (cartierToPicardPoints_natural f D C)
  exact h.trans ((cartierToPicardPoints_apply f D C C.dual.X (𝟙 C.dual.X)).trans (Category.id_comp _))

theorem cartierToPicard_isMonHom :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    IsMonHom (ParameterizedCharacterLines.Construction.KernelCharacters.cartierToPicard f D C) := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  rw [← cartierToPicardGroup_underlying f D C]
  infer_instance

variable (n : ℕ) (hn : ∀ (T : Over S) (x : T ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)

/-- The actual torsion factor preserves the inherited group law. -/
theorem cartierToPicardTorsion_isMonHom :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    IsMonHom (CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion f D n hn C) := by
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  have : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
  have : Mono (TorsionQuotient.SubgroupFunctor.torsionι D.abelian n) := inferInstanceAs (Mono (equalizer.ι ((𝟙 D.abelian) ^ n) 1))
  have : IsMonHom (CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion f D n hn C ≫ TorsionQuotient.SubgroupFunctor.torsionι D.abelian n) := by
    rw [CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion_inclusion]
    exact cartierToPicard_isMonHom f D C
  exact Picard.PoincareBundle.Kernel.Splitting.isMonHom_of_mono_postcomp _ (TorsionQuotient.SubgroupFunctor.torsionι D.abelian n)

/-- The actual Cartier-to-dual-torsion morphism, as a native group-scheme homomorphism. -/
def cartierToPicardTorsionGroup :
    letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
    letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
    C.dual ⟶ TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk D.abelian) n :=
  letI := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup D
  letI : IsCommMonObj D.abelian := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup_commutative D
  @Grp.homMk (Over S) _ _ C.dual (TorsionSheaves.Construction.Schemes.nativeTorsionGroup (Grp.mk D.abelian) n)
    (CharacterTorsionFactor.Construction.KernelCharacters.cartierToPicardTorsion f D n hn C) (cartierToPicardTorsion_isMonHom f D C n hn)

end Construction.KernelCharacters

end

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.PicardHomomorphism
