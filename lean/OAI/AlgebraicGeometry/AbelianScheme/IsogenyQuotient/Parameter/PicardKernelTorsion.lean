import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Canonical.PicardKernelTorsion

/-! # Picard Kernel Torsion -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.PicardKernelTorsion.Construction

noncomputable section

/-! A constant degree only on the chosen parameter and its restrictions
suffices for the norm bound on the actual Picard pullback kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

universe u
variable {S : Scheme.{u}} {A B : Over S} [GrpObj A] [GrpObj B]
  (f : A ⟶ B) [IsMonHom f] [IsFinite f.left] [Flat f.left] [LocallyOfFinitePresentation f.left]

set_option backward.isDefEq.respectTransparency false in
theorem homogeneousPicardPullback_kernel_pow_on_parameter (d : ℕ) (T : Over S)
    (hdegree : ∀ (U : Over S) [IsAffine U.left] (_a : U ⟶ T)
      (b : (U ⊗ B).left), (U ◁ f).left.finrank b = d)
    (y : (Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B).obj.obj (op T))
    (hy : UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom f T y = 1) : y ^ d = 1 := by
  let J := Scheme.fppfTopology.over S
  let F := Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.homogeneousPicardSheaf B
  let R := Presheaf.equalizerSieve (F := F.obj) (y ^ d) 1
  have hR : R ∈ J T := by
    apply Picard.KernelLocalClasses.Construction.picardPullbackKernel_cover_of_class_lifts f T y
      (UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullback_kernel_relative f T y
        ((UnbundledPicardPullbackHom.Construction.nativeHomogeneousPicardPullbackHom_apply f T y).symm.trans hy)) R
    intro U _ a c hc hcy
    obtain ⟨L, rfl⟩ := Quotient.exists_rep c
    have hp := Picard.PullbackKernelTorsion.Construction.parameterProductMap_isPullback f U
    have : IsFinite (U ◁ f).left := MorphismProperty.of_isPullback hp inferInstance
    have : Flat (U ◁ f).left := MorphismProperty.of_isPullback hp inferInstance
    have : LocallyOfFinitePresentation (U ◁ f).left := MorphismProperty.of_isPullback hp inferInstance
    have hpow := Finite.FlatPicardKernelPower.Construction.finiteFlatPullbackKernel_class_pow (U ◁ f).left L d (hdegree U a) hc
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
    exact (congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B).app (op U)) hpow).trans (Picard.Homomorphisms.RelativeGroup.Construction.trivialPicardClass_eq_one B U)
  have hF : Presieve.IsSheaf J F.obj := (isSheaf_iff_isSheaf_of_type _ _).mp F.property
  exact (hF R hR).isSeparatedFor.ext (by intro U a ha; exact ha)

set_option backward.isDefEq.respectTransparency false in
theorem canonicalPicardPullback_kernel_pow_on_parameter {S : Scheme.{u}} {g : ℕ}
    {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) {X : Over S} [GrpObj X]
    (f : X ⟶ A.scheme) [IsMonHom f] [IsFinite f.left] [Flat f.left] [LocallyOfFinitePresentation f.left]
    (d : ℕ) (T : Over S)
    (hdegree : ∀ (U : Over S) [IsAffine U.left] (_a : U ⟶ T)
      (b : (U ⊗ A.scheme).left), (U ◁ f).left.finrank b = d)
    (z : T ⟶ (Canonical.DualData.Construction.canonicalDualAbelianData D).abelian.scheme)
    (hz : Canonical.PicardPullback.Construction.canonicalPicardPullbackHom D f T z = 1) : z ^ d = 1 := by
  have h := homogeneousPicardPullback_kernel_pow_on_parameter f d T hdegree
    ((Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D).representable.homEquiv z) hz
  let := Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroup (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D)
  apply (Picard.Homomorphisms.UnbundledDualGroup.Construction.UnbundledPicard.dualPicardGroupHomEquiv (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D) T).injective
  rw [map_pow, map_one]
  exact h

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.PicardKernelTorsion.Construction
