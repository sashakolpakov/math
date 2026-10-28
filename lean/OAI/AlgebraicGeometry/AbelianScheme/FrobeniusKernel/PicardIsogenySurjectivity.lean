import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardEndoisogenyEpi
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCommutativeComposition
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCommutative
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCharacterSourceSquare
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EpiFromLift

/-! # Picard Isogeny Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardIsogenySurjectivity.Construction

noncomputable section

/-! Picard pullback is locally surjective onto the quotient's Picard
sheaf. Only the original dual and actual isogenies in both directions
are used; no dual of the quotient is an input. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {d h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A)

include D f in
theorem picardPullback_epi_with_return_isogeny :
    Epi (PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback B A g.hom) := by
  let m : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A A := {
    hom := f.hom ≫ g.hom
    preservesGroup := inferInstance
    finite := inferInstanceAs (IsFinite (f.hom.left ≫ g.hom.left))
    flat := inferInstanceAs (Flat (f.hom.left ≫ g.hom.left))
    surjective := inferInstanceAs (Surjective (f.hom.left ≫ g.hom.left)) }
  have hmfinite : IsFinite m.hom.left := m.finite
  have hmflat : Flat m.hom.left := m.flat
  have hmsurjective : Surjective m.hom.left := m.surjective
  have hfp : LocallyOfFinitePresentation f.hom.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType (by rw [f.hom.w]; infer_instance) inferInstance
  have hmp : LocallyOfFinitePresentation m.hom.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType (by rw [m.hom.w]; infer_instance) inferInstance
  have hKf := Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree f.hom ⟨inferInstance, inferInstance, inferInstance⟩
  have hKm := Picard.Homomorphisms.Kernel.Construction.kernelScheme_finiteLocallyFree m.hom ⟨hmfinite, hmflat, hmp⟩
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom).hom := hKf.1
  have : Flat (Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom).hom := hKf.2.1
  have : LocallyOfFinitePresentation (Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom).hom := hKf.2.2
  have : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme m.hom).hom := hKm.1
  have : Flat (Picard.Homomorphisms.Kernel.Construction.kernelScheme m.hom).hom := hKm.2.1
  have : LocallyOfFinitePresentation (Picard.Homomorphisms.Kernel.Construction.kernelScheme m.hom).hom := hKm.2.2
  have : IsCommMonObj (Picard.Homomorphisms.Kernel.Construction.kernelScheme f.hom) := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemeGroup_commutative f.hom
  have : IsCommMonObj (Picard.Homomorphisms.Kernel.Construction.kernelScheme m.hom) := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemeGroup_commutative m.hom
  let w : (𝟙 A.scheme) ≫ m.hom = f.hom ≫ g.hom := Category.id_comp _
  let i := ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap m.hom f.hom (𝟙 A.scheme) g.hom w
  have hi : i.hom.hom ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion m.hom = Picard.Homomorphisms.Kernel.Construction.kernelInclusion f.hom :=
    (CharacterSourceMap.Construction.kernelSourceSquareMap_inclusion m.hom f.hom (𝟙 A.scheme) g.hom w).trans (Category.comp_id _)
  have : Mono (i.hom.hom ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion m.hom) := hi.symm ▸ inferInstance
  have : Mono i.hom.hom := mono_of_mono i.hom.hom (Picard.Homomorphisms.Kernel.Construction.kernelInclusion m.hom)
  have hiEpi : Epi (IntrinsicCharacterRestrictionEpi.Construction.nativeCharacterRestriction i) := IntrinsicCharacterRestrictionEpi.Construction.nativeCharacterRestriction_epi i
  let r := IntrinsicCharacterRestrictionEpi.Construction.nativeCharacterRestriction i ≫ (PicardCommutative.Construction.characterPicardFppfKernelIso A B f.hom).hom
  have hr : Epi r := epi_comp' hiEpi
    (inferInstanceAs (Epi (PicardCommutative.Construction.characterPicardFppfKernelIso A B f.hom).hom))
  have he : Epi (PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback B A g.hom ≫ PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A B f.hom) := by
    rw [← PicardCommutativeComposition.Construction.homogeneousPicardFppfPullback_comp A B A f.hom g.hom]
    exact PicardEndoisogenyEpi.Construction.homogeneousPicardFppfPullback_endoisogeny_epi D m
  refine @EpiFromLift.Construction.epi_of_composite_epi_of_kernel_lift (CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb (Spec (.of k))) inferInstance inferInstance
    _ _ _ _ (PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback B A g.hom)
    (PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A B f.hom) he r hr (PicardCommutativeSheaf.Construction.characterToPicardFppfAb A A m.hom) ?_
  change PicardCommutativeSheaf.Construction.characterToPicardFppfAb A A m.hom ≫ PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback B A g.hom =
    (IntrinsicCharacterRestrictionEpi.Construction.nativeCharacterRestriction i ≫ (PicardCommutative.Construction.characterPicardFppfKernelIso A B f.hom).hom) ≫ _
  have hs := PicardCharacterSourceSquare.Construction.characterToPicardFppfAb_source A A A B m.hom f.hom (𝟙 A.scheme) g.hom w
  have hk := congrArg (fun z => IntrinsicCharacterRestrictionEpi.Construction.nativeCharacterRestriction i ≫ z)
    (PicardCommutative.Construction.characterPicardFppfKernelIso_inclusion A B f.hom)
  exact hs.trans (hk.symm.trans
    (Category.assoc (IntrinsicCharacterRestrictionEpi.Construction.nativeCharacterRestriction i) (PicardCommutative.Construction.characterPicardFppfKernelIso A B f.hom).hom
      (kernel.ι (PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A B f.hom))).symm)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardIsogenySurjectivity.Construction
