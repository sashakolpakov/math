import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.KernelLocalClasses
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.LineKernelCharacter

/-! # Character Iso Picard Lifting -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CharacterIsoPicardLifting.Construction

noncomputable section

/-! An actual character-kernel isomorphism with its line-class recovery
lifts every section of the Picard pullback kernel fppf locally. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {k : Type u} [Field k] {A B C K : Over (Spec (.of k))}
  [GrpObj A] [GrpObj B]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (Y : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation _ (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (v : K ⟶ C) (c : K ⟶ Y.dual.X) [IsIso c]
  (hc : ∀ (T : Over (Spec (.of k))) (x : T ⟶ K),
    CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (Y.sectionEquiv T (x ≫ c)) =
      i.app (op T) (ULift.up (x ≫ v)))

include hc in
set_option backward.isDefEq.respectTransparency false in
theorem characterIso_picardKernel_cover
    (T : Over (Spec (.of k))) (y : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
    (hy : (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f).hom.app (op T)
      ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op T) y) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) :
    Presheaf.imageSieve i y ∈ (Scheme.fppfTopology.over (Spec (.of k))) T := by
  apply Picard.KernelLocalClasses.Construction.picardPullbackKernel_cover_of_class_lifts f T y hy
  intro U _ a d hd hyU
  obtain ⟨L, rfl⟩ := Quotient.exists_rep d
  have hL : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback ((𝟙 U) ⊗ₘ f).left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (U ⊗ A).left := by
    rw [id_tensorHom]
    exact hd
  obtain ⟨χ, hχ⟩ := Product.LineKernelCharacter.Construction.exists_kernelCharacter_of_productLine_pullback_trivial f U L hL
    ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map a.op y) hyU
  let x := (Y.sectionEquiv U).symm χ ≫ inv c
  have hx : Y.sectionEquiv U (x ≫ c) = χ := by
    rw [show x = (Y.sectionEquiv U).symm χ ≫ inv c from rfl,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact (Y.sectionEquiv U).apply_symm_apply χ
  refine ⟨ULift.up (x ≫ v), ?_⟩
  exact (hc U x).symm.trans ((congrArg (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f U) hx).trans hχ)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CharacterIsoPicardLifting.Construction
