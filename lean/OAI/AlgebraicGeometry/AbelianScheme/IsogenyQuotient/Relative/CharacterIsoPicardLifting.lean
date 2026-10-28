import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.FamilyPicardKernelCover
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.KernelLocalClassCovers
import OAI.AlgebraicGeometry.FormalGeometry.Completion.FppfPairLift

/-! # Character Iso Picard Lifting -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CharacterIsoPicardLifting.Construction

noncomputable section

/-! An isomorphism to the actual Cartier kernel with its character
line values lifts every relative Picard pullback-kernel section
locally over an arbitrary characteristic-zero base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B C K : Over S} [GrpObj A] [GrpObj B]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
  (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (Y : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (v : K ⟶ C) (c : K ⟶ Y.dual.X) [IsIso c]
  (hc : ∀ (T : Over S) (x : T ⟶ K),
    CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (Y.sectionEquiv T (x ≫ c)) =
      i.app (op T) (ULift.up (x ≫ v)))

include hc in
set_option backward.isDefEq.respectTransparency false in
theorem relativeCharacterIso_picardKernel_cover
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)
    (T : Over S) (y : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
    (hy : (Picard.Homomorphisms.SheafMaps.Construction.relativePicardPullback f).hom.app (op T)
      ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op T) y) = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A T) :
    Presheaf.imageSieve i y ∈ (Scheme.fppfTopology.over S) T := by
  let J := Scheme.fppfTopology.over S
  apply Picard.KernelLocalClassCovers.Construction.picardPullbackKernel_cover_of_local_class_lifts f T y hy
  intro U _ a d hd hyU
  obtain ⟨L, rfl⟩ := Quotient.exists_rep d
  have hL : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback ((𝟙 U) ⊗ₘ f).left) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass (U ⊗ A).left := by
    rw [id_tensorHom]
    exact hd
  obtain ⟨P, b, hb, hs, χ, hχ⟩ := FamilyPicardKernelCover.Construction.exists_familyPicardKernelCharacter_cover f Y p n hn hk U L hL
    ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map a.op y) hyU
  have : Etale b.left := hb
  have : Surjective b.left := hs
  apply J.superset_covering _ (FormalGeometry.Completion.FppfSheafSectionDescent.Construction.fppfSingleton_cover b)
  apply (Sieve.generate_le_iff _ _).mpr
  intro V d hd
  cases hd
  let x := (Y.sectionEquiv P).symm χ ≫ inv c
  have hx : Y.sectionEquiv P (x ≫ c) = χ := by
    rw [show x = (Y.sectionEquiv P).symm χ ≫ inv c from rfl,
      Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    exact (Y.sectionEquiv P).apply_symm_apply χ
  refine ⟨ULift.up (x ≫ v), ?_⟩
  have hv := (hc P x).symm.trans ((congrArg (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f P) hx).trans hχ)
  exact hv.trans ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.map_comp_apply a.op b.op y).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CharacterIsoPicardLifting.Construction
