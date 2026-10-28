import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SectionHomLocalSurjectivity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnbundledPicardPullbackHom
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CharacterIsoPicardLifting
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.SourceLocalSurjectivity

/-! # Sheaf Iso -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SheafIso.Construction

noncomputable section

/-! Kernel-character recovery and the actual fppf source map prove
that the abelian Picard image represents the entire homogeneous Picard sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {k : Type u} [Field k] {A B C K : Over (Spec (.of k))}
  [GrpObj A] [GrpObj B] [GrpObj C] [IsCommMonObj C]
  [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
  (D : Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData A) (f : A ⟶ B) [IsMonHom f]
  [IsFinite f.left] [Flat f.left] [Surjective f.left] [LocallyOfFinitePresentation f.left]
  (Y : CartierDuality.GroupRepresentatives.Construction.Schemes.CharacterGroupRepresentation _ (Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)))
  (i : uliftYoneda.{u + 1}.obj C ⟶ (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj)
  (F : ∀ T : Over (Spec (.of k)), (T ⟶ C) →* (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
  (hF : ∀ (T : Over (Spec (.of k))) (x : T ⟶ C), F T x = i.app (op T) (ULift.up x))
  (v : K ⟶ C) (c : K ⟶ Y.dual.X) [IsIso c]
  (hc : ∀ (T : Over (Spec (.of k))) (x : T ⟶ K),
    CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f T (Y.sectionEquiv T (x ≫ c)) = i.app (op T) (ULift.up (x ≫ v)))
  [Flat (SourceMap.Construction.picardImageSourceMap D f i).left] [Surjective (SourceMap.Construction.picardImageSourceMap D f i).left]
  [LocallyOfFinitePresentation (SourceMap.Construction.picardImageSourceMap D f i).left]

include D F hF v c hc in
set_option backward.isDefEq.respectTransparency false in
theorem picardImage_locallySurjective_of_character_iso :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k))) i := by
  let (T : (Over (Spec (.of k)))ᵒᵖ) : CommGroup ((uliftYoneda.{u + 1}.obj C).obj T) :=
    inferInstanceAs (CommGroup (ULift.{u + 1} (T.unop ⟶ C)))
  let FI (T : Over (Spec (.of k))) : (uliftYoneda.{u + 1}.obj C).obj (op T) →*
      (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T) := {
    toFun := fun x => F T x.down
    map_one' := (F T).map_one
    map_mul' x y := (F T).map_mul x.down y.down }
  have := Picard.SourceLocalSurjectivity.Construction.picardImageSource_pullback_locallySurjective D f i
  apply SectionHomLocalSurjectivity.Construction.locallySurjective_of_section_homs _ i (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback A B f).hom
    FI
    (fun T x => hF T x.down)
    (UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f) (UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom_apply f)
    (fun a => Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf B) a.op)
    (fun a x => Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom_apply (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf B) a.op x)
  intro T y hy
  exact CharacterIsoPicardLifting.Construction.characterIso_picardKernel_cover f Y i v c hc T y
    (UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullback_kernel_relative f T y hy)

include D F hF v c hc in
theorem picardImage_isIso_of_character_iso [Mono i] : IsIso i := by
  have hs : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over (Spec (.of k))) i :=
    picardImage_locallySurjective_of_character_iso D f Y i F hF v c hc
  have hi : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over (Spec (.of k))) i := by
    constructor
    intro T x y hxy
    have hinj : Function.Injective (i.app T) := (CategoryTheory.mono_iff_injective _).mp inferInstance
    rw [hinj hxy, Presheaf.equalizerSieve_self_eq_top]
    exact (Scheme.fppfTopology.over (Spec (.of k))).top_mem _
  let j : CartierDuality.CharacterFunctor.Construction.Schemes.pointSheaf _ C ⟶ Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B := ⟨i⟩
  have : Sheaf.IsLocallySurjective j := hs
  have : Sheaf.IsLocallyInjective j := hi
  have : IsIso j := (Sheaf.isLocallyBijective_iff_isIso j).mp ⟨inferInstance, inferInstance⟩
  exact (sheafToPresheaf _ _).map_isIso j

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PicardImage.SheafIso.Construction
