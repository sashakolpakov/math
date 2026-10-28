import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Finite.FlatPicardKernelPower
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.KernelLocalClasses
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnbundledPicardPullbackHom
import OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection

/-! # Pullback Kernel Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.PullbackKernelTorsion.Construction

noncomputable section

/-! A finite-flat map of constant degree kills its full homogeneous
Picard pullback kernel by that degree. The proof uses actual norm
sections and fppf local line representatives over arbitrary bases. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.Homomorphisms.UnbundledPoincareDetection.Construction.UnbundledPicard

universe u

theorem parameterProductMap_isPullback {S : Scheme.{u}} {A B : Over S}
    (f : A ⟶ B) (T : Over S) :
    IsPullback (snd T A).left (T ◁ f).left f.left (snd T B).left := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback T.hom B.hom).flip
  · have he : (T ◁ f).left ≫ (fst T B).left = (fst T A).left :=
      congrArg Over.Hom.left (whiskerLeft_fst T f)
    rw [Over.w f]
    change IsPullback (snd T A).left ((T ◁ f).left ≫ (fst T B).left) A.hom T.hom
    rw [he]
    exact (IsPullback.of_hasPullback T.hom A.hom).flip
  · exact (congrArg Over.Hom.left (whiskerLeft_snd T f)).symm

variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left] [LocallyOfFinitePresentation f.left]
  (d : ℕ) (hdegree : ∀ b : B.left, f.left.finrank b = d)

include hdegree in
set_option backward.isDefEq.respectTransparency false in
theorem homogeneousPicardPullback_kernel_pow (T : Over S)
    (y : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
    (hy : UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f T y = 1) : y ^ d = 1 := by
  let J := Scheme.fppfTopology.over S
  let F := Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B
  let R := Presheaf.equalizerSieve (F := F.obj) (y ^ d) 1
  have hR : R ∈ J T := by
    apply KernelLocalClasses.Construction.picardPullbackKernel_cover_of_class_lifts f T y
      (UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullback_kernel_relative f T y
        ((UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom_apply f T y).symm.trans hy)) R
    intro U _ a c hc hcy
    obtain ⟨L, rfl⟩ := Quotient.exists_rep c
    have hp := parameterProductMap_isPullback f U
    have : IsFinite (U ◁ f).left := MorphismProperty.of_isPullback hp inferInstance
    have : Flat (U ◁ f).left := MorphismProperty.of_isPullback hp inferInstance
    have : LocallyOfFinitePresentation (U ◁ f).left := MorphismProperty.of_isPullback hp inferInstance
    have hd : ∀ b : (U ⊗ B).left, (U ◁ f).left.finrank b = d := fun b =>
      (Scheme.Hom.finrank_of_isPullback _ _ _ _ hp b).trans (hdegree _)
    have hpow := Finite.FlatPicardKernelPower.Construction.finiteFlatPullbackKernel_class_pow (U ◁ f).left L d hd hc
    change F.obj.map a.op (y ^ d) = F.obj.map a.op 1
    have hmap : F.obj.map a.op (y ^ d) = (F.obj.map a.op y) ^ d := by
      have h := (Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf B) a.op).map_pow y d
      simp only [Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom_apply] at h
      exact h
    have hone : F.obj.map a.op 1 = 1 := by
      have h := (Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom (Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardGroupPresheaf B) a.op).map_one
      simp only [Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom_apply] at h
      exact h
    rw [hmap, hone]
    have hm : Mono ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op U)) := inferInstance
    apply (CategoryTheory.mono_iff_injective _).mp hm
    rw [← Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom_apply,
      ← Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom_apply, map_pow, map_one,
      Picard.Homomorphisms.UnbundledGroup.Construction.UnbundledPicard.homogeneousPicardSheafInclusionHom_apply]
    change ((Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheafInclusion B).hom.app (op U) (F.obj.map a.op y)) ^ d = 1
    rw [← hcy, ← Picard.Homomorphisms.RelativeGroup.Construction.toRelativePicard_pow]
    exact (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op U)) hpow).trans
      (Picard.Homomorphisms.RelativeGroup.Construction.trivialPicardClass_eq_one B U)
  have hF : Presieve.IsSheaf J F.obj := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  exact (hF R hR).isSeparatedFor.ext (by intro U a ha; exact ha)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Picard.PullbackKernelTorsion.Construction
