import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CartierCharacterPicardMap
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CharacterIsoPicardLifting
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.MonoSheafLocalImage

/-! # Cartier Picard Kernel -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CartierPicardKernel.Construction

noncomputable section

/-! The actual Cartier dual represents the complete relative Picard
pullback kernel over an arbitrary characteristic-zero base. Existence
uses the constructed covers and uniqueness uses the character-line
injection, so all nonreduced parameter schemes are retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
  (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (C : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))

set_option backward.isDefEq.respectTransparency false in
theorem cartierCharacterPicardSheafMap_kernel_cover
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)
    (T : Over S) (y : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
    (hy : UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f T y = 1) :
    Presheaf.imageSieve (CartierCharacterPicardMap.Construction.cartierCharacterPicardSheafMap f C) y ∈ (Scheme.fppfTopology.over S) T := by
  refine CharacterIsoPicardLifting.Construction.relativeCharacterIso_picardKernel_cover f C (CartierCharacterPicardMap.Construction.cartierCharacterPicardSheafMap f C)
    (𝟙 C.dual.X) (𝟙 C.dual.X) ?_ p n hn hk T y ?_
  · intro U x
    simp only [Category.comp_id, CartierCharacterPicardMap.Construction.cartierCharacterPicardSheafMap_apply]
  · exact UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullback_kernel_relative f T y
      ((UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom_apply f T y).symm.trans hy)

set_option backward.isDefEq.respectTransparency false in
theorem cartierCharacterPicardSheafMap_kernel_existsUnique
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)
    (T : Over S) (y : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
    (hy : UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f T y = 1) :
    ∃! x : (uliftYoneda.{u + 1}.obj C.dual.X).obj (op T),
      (CartierCharacterPicardMap.Construction.cartierCharacterPicardSheafMap f C).app (op T) x = y := by
  let i := CartierCharacterPicardMap.Construction.cartierCharacterPicardSheafMap f C
  have : Mono i := CartierCharacterPicardMap.Construction.cartierCharacterPicardSheafMap_mono f C n
    (DegreeBaseChange.Construction.positiveNat_isUnit_on_charZero_field_scheme p n hn) hk
  let j : CartierDuality.CharacterFunctor.Construction.Schemes.pointSheaf S C.dual.X ⟶ Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B := ⟨i⟩
  have : Mono j.hom := ‹Mono i›
  have hcover := cartierCharacterPicardSheafMap_kernel_cover f C p n hn hk T y hy
  exact MonoSheafLocalImage.Construction.existsUnique_preimage_of_covering_imageSieve j T y hcover

theorem relativePicardPullbackKernel_existsUnique_cartierPoint
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)
    (T : Over S) (y : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
    (hy : UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f T y = 1) :
    ∃! x : T ⟶ C.dual.X, CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (C.sectionEquiv T x) = y := by
  obtain ⟨x, hx, hu⟩ := cartierCharacterPicardSheafMap_kernel_existsUnique f C p n hn hk T y hy
  have hv := (CartierCharacterPicardMap.Construction.cartierCharacterPicardSheafMap_apply f C T x.down).symm.trans hx
  refine ⟨x.down, hv, ?_⟩
  intro x' hx'
  exact congrArg ULift.down (hu (ULift.up x')
    ((CartierCharacterPicardMap.Construction.cartierCharacterPicardSheafMap_apply f C T x').trans hx'))

theorem relativePicardPullbackKernel_iff_cartierPoint
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1)
    (T : Over S) (y : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T)) :
    UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f T y = 1 ↔
      ∃! x : T ⟶ C.dual.X, CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (C.sectionEquiv T x) = y := by
  constructor
  · exact relativePicardPullbackKernel_existsUnique_cartierPoint f C p n hn hk T y
  · rintro ⟨x, hx, _⟩
    rw [← hx]
    exact Parameter.CharacterPullback.Construction.parameterCharacterPicardHom_pullback_one f T (C.sectionEquiv T x)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CartierPicardKernel.Construction
