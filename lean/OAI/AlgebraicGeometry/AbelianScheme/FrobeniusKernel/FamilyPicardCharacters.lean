import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ParameterPicardSurjectivity
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterPicard

/-! # Family Picard Characters -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyPicardCharacters

noncomputable section

/-! The exact kernel of pullback on family line classes over an affine
test scheme is the group of actual kernel-character sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace Construction

universe u

variable {k : Type u} [Field k]
variable {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B]
variable [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
variable (f : A ⟶ B) [IsMonHom f]
variable [IsFinite f.left] [Flat f.left] [Surjective f.left]
  [LocallyOfFinitePresentation f.left]
variable (Q : Over (Spec (.of k))) [IsAffine Q.left]

theorem familyLine_kernel_character_exists (c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (Q ⊗ B).left)
    (hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Q ◁ f).left c = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (Q ⊗ A).left) :
    ∃ χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q),
      c = CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B Q (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ) := by
  let eA : (Q ⊗ A).left ≅ ((Over.pullback Q.hom).obj A).left := pullbackSymmetry Q.hom A.hom
  let eB : (Q ⊗ B).left ≅ ((Over.pullback Q.hom).obj B).left := pullbackSymmetry Q.hom B.hom
  let c' := (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackIso eB).symm c
  have hec : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass eB.hom c' = c := (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackIso eB).apply_symm_apply c
  have hs : (Q ◁ f).left ≫ eB.hom = eA.hom ≫ ((Over.pullback Q.hom).map f).left := by
    have h := CharacterPicard.Construction.characterParameterFamilyMap_square f Q
    rw [CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_eq_symmetry, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_eq_symmetry] at h
    exact h
  have hk : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left c' =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass ((Over.pullback Q.hom).obj A).left := by
    apply (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackIso eA).injective
    change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass eA.hom
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left c') =
        AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass eA.hom (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass _)
    rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← hs, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp,
      hec, hc, AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_trivial]
  obtain ⟨L, hL⟩ := Quotient.exists_rep c'
  have hframe : Nonempty
      ((Scheme.Modules.pullback ((Over.pullback Q.hom).map f).left).obj L.sheaf ≅
        AbelianModuli.HilbertConstruction.Line.Bundles.structureModule ((Over.pullback Q.hom).obj A).left) :=
    Quotient.exact ((congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((Over.pullback Q.hom).map f).left) hL).trans hk)
  obtain ⟨χ, hχ⟩ := ParameterPicardSurjectivity.Construction.parameterLine_kernel_character_exists f Q L hframe.some
  refine ⟨χ, ?_⟩
  have hp : c = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass eB.hom (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) :=
    (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass eB.hom) hL).trans hec |>.symm
  have he : c = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass eB.hom (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ)) :=
    hp.trans (congrArg (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass eB.hom) (Quotient.sound hχ))
  exact he.trans (by
    rw [CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass, CartierDuality.ParameterFamily.Construction.KernelCharacters.parameterFamilyMap_eq_symmetry]
    rfl)

theorem familyLine_kernel_character_unique (c : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (Q ⊗ B).left)
    (hc : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (Q ◁ f).left c = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (Q ⊗ A).left) :
    ∃! χ : (CartierDuality.CharacterSheaf.Construction.Schemes.characterSheaf (Spec (.of k)) (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f))).obj.obj (.op Q),
      c = CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterLineClass B Q (CartierDuality.ParameterizedCharacterLines.Construction.KernelCharacters.parameterCharacterLine f Q χ) := by
  obtain ⟨χ, hχ⟩ := familyLine_kernel_character_exists f Q c hc
  refine ⟨χ, hχ, ?_⟩
  intro ψ hψ
  have : IsIso ((Over.pullback Q.hom).obj A).hom.appTop := CartierDuality.CharacterLineFaithfulness.Construction.KernelCharacters.properGroup_parameter_appTop_isIso A Q
  exact CartierDuality.CharacterLineFaithfulness.Construction.KernelCharacters.parameterLineClass_injective f Q
    (ConcreteCategory.bijective_of_isIso ((Over.pullback Q.hom).obj A).hom.appTop).surjective
    (hψ.symm.trans hχ)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.FamilyPicardCharacters
