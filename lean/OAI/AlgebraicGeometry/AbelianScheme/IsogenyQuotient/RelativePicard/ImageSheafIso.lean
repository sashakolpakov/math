import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.CharacterIsoPicardLifting
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SectionHomLocalSurjectivity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnbundledPicardPullbackHom
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.SourceLocalSurjectivity

/-! # Image Sheaf Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.ImageSheafIso.Construction

noncomputable section

/-! The full Picard image criterion over an arbitrary characteristic-zero
base uses actual local character recovery. Its source map and Cartier
kernel identification remain explicit hypotheses of this criterion. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B C K : Over S} [GrpObj A] [GrpObj B] [GrpObj C] [IsCommMonObj C]
  [IsProper A.hom] [Smooth A.hom] [GeometricallyConnected A.hom]
  [IsProper B.hom] [Smooth B.hom] [GeometricallyConnected B.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (Y : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation S (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (F : ∀ T : Over S, (T ⟶ C) →* (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
  (hF : ∀ (T : Over S) (x : T ⟶ C), F T x = i.app (op T) (ULift.up x))
  (v : K ⟶ C) (c : K ⟶ Y.dual.X) [IsIso c]
  (hc : ∀ (T : Over S) (x : T ⟶ K),
    CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (Y.sectionEquiv T (x ≫ c)) = i.app (op T) (ULift.up (x ≫ v)))
  [Flat (PicardImage.SourceMap.Construction.picardImageSourceMap D f i).left] [Surjective (PicardImage.SourceMap.Construction.picardImageSourceMap D f i).left]
  [LocallyOfFinitePresentation (PicardImage.SourceMap.Construction.picardImageSourceMap D f i).left]

include D F hF v c hc in
set_option backward.isDefEq.respectTransparency false in
theorem relativePicardImage_locallySurjective_of_character_iso
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) i := by
  let (T : (Over S)ᵒᵖ) : CommGroup ((uliftYoneda.{u + 1}.obj C).obj T) :=
    inferInstanceAs (CommGroup (ULift.{u + 1} (T.unop ⟶ C)))
  let FI (T : Over S) : (uliftYoneda.{u + 1}.obj C).obj (op T) →*
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T) := {
    toFun := fun x => F T x.down
    map_one' := (F T).map_one
    map_mul' x y := (F T).map_mul x.down y.down }
  have := Picard.SourceLocalSurjectivity.Construction.picardImageSource_pullback_locallySurjective D f i
  apply SectionHomLocalSurjectivity.Construction.locallySurjective_of_section_homs _ i (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom
    FI (fun T x => hF T x.down)
    (UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f) (UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom_apply f)
    (fun a => Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf B) a.op)
    (fun a x => Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom_apply (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf B) a.op x)
  intro T y hy
  exact Relative.CharacterIsoPicardLifting.Construction.relativeCharacterIso_picardKernel_cover f Y i v c hc p n hn hk T y
    (UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullback_kernel_relative f T y hy)

include D F hF v c hc in
theorem relativePicardImage_isIso_of_character_iso [Mono i]
    {k : Type u} [Field k] [CharZero k] (p : S ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) (hk : ∀ (U : Over S) (x : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme f), x ^ n = 1) :
    IsIso i := by
  have hs : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) i :=
    relativePicardImage_locallySurjective_of_character_iso D f Y i F hF v c hc p n hn hk
  have hi : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) i := by
    constructor
    intro T x y hxy
    have hinj : Function.Injective (i.app T) := (CategoryTheory.mono_iff_injective _).mp inferInstance
    rw [hinj hxy, Presheaf.equalizerSieve_self_eq_top]
    exact (Scheme.fppfTopology.over S).top_mem _
  let j : CartierDuality.CharacterFunctor.Construction.Schemes.pointSheaf S C ⟶ Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B := ⟨i⟩
  have : Sheaf.IsLocallySurjective j := hs
  have : Sheaf.IsLocallyInjective j := hi
  have : IsIso j := (Sheaf.isLocallyBijective_iff_isIso j).mp ⟨inferInstance, inferInstance⟩
  exact (sheafToPresheaf _ _).map_isIso j

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.RelativePicard.ImageSheafIso.Construction
