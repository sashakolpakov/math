import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.PicardEndoisogeny
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCommutativeComposition
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCommutative
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardCharacterSourceSquare
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EpiFromLift
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricQuotientSheafCokernel

/-! # Picard Presentation -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Field.PicardPresentation.Surjectivity

/-! Picard pullback is locally surjective onto the quotient's Picard
sheaf. Only the original dual and actual isogenies in both directions
are used; no dual of the quotient is an input. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] {d : ℕ}
variable {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) (g : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A)

include D f in
theorem picardPullback_epi_with_return_isogeny :
    Epi (AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback B A g.hom) := by
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
  let i := AbelianScheme.FrobeniusKernel.ParameterCharacterSourceRestriction.Construction.kernelSourceSquareGroupMap m.hom f.hom (𝟙 A.scheme) g.hom w
  have hi : i.hom.hom ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion m.hom = Picard.Homomorphisms.Kernel.Construction.kernelInclusion f.hom :=
    (AbelianScheme.FrobeniusKernel.CharacterSourceMap.Construction.kernelSourceSquareMap_inclusion m.hom f.hom (𝟙 A.scheme) g.hom w).trans (Category.comp_id _)
  have : Mono (i.hom.hom ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion m.hom) := hi.symm ▸ inferInstance
  have : Mono i.hom.hom := mono_of_mono i.hom.hom (Picard.Homomorphisms.Kernel.Construction.kernelInclusion m.hom)
  have hiEpi : Epi (AbelianScheme.FrobeniusKernel.IntrinsicCharacterRestrictionEpi.Construction.nativeCharacterRestriction i) := AbelianScheme.FrobeniusKernel.IntrinsicCharacterRestrictionEpi.Construction.nativeCharacterRestriction_epi i
  let r := AbelianScheme.FrobeniusKernel.IntrinsicCharacterRestrictionEpi.Construction.nativeCharacterRestriction i ≫ (AbelianScheme.FrobeniusKernel.PicardCommutative.Construction.characterPicardFppfKernelIso A B f.hom).hom
  have hr : Epi r := epi_comp' hiEpi
    (inferInstanceAs (Epi (AbelianScheme.FrobeniusKernel.PicardCommutative.Construction.characterPicardFppfKernelIso A B f.hom).hom))
  have he : Epi (AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback B A g.hom ≫ AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A B f.hom) := by
    rw [← AbelianScheme.FrobeniusKernel.PicardCommutativeComposition.Construction.homogeneousPicardFppfPullback_comp A B A f.hom g.hom]
    exact PicardEndoisogeny.homogeneousPicardFppfPullback_endoisogeny_epi D m
  refine @AbelianScheme.FrobeniusKernel.EpiFromLift.Construction.epi_of_composite_epi_of_kernel_lift (AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb (Spec (.of k))) inferInstance inferInstance
    _ _ _ _ (AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback B A g.hom)
    (AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A B f.hom) he r hr (AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.characterToPicardFppfAb A A m.hom) ?_
  change AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.characterToPicardFppfAb A A m.hom ≫ AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback B A g.hom =
    (AbelianScheme.FrobeniusKernel.IntrinsicCharacterRestrictionEpi.Construction.nativeCharacterRestriction i ≫ (AbelianScheme.FrobeniusKernel.PicardCommutative.Construction.characterPicardFppfKernelIso A B f.hom).hom) ≫ _
  have hs := AbelianScheme.FrobeniusKernel.PicardCharacterSourceSquare.Construction.characterToPicardFppfAb_source A A A B m.hom f.hom (𝟙 A.scheme) g.hom w
  have hk := congrArg (fun z => AbelianScheme.FrobeniusKernel.IntrinsicCharacterRestrictionEpi.Construction.nativeCharacterRestriction i ≫ z)
    (AbelianScheme.FrobeniusKernel.PicardCommutative.Construction.characterPicardFppfKernelIso_inclusion A B f.hom)
  exact hs.trans (hk.symm.trans
    (Category.assoc (AbelianScheme.FrobeniusKernel.IntrinsicCharacterRestrictionEpi.Construction.nativeCharacterRestriction i) (AbelianScheme.FrobeniusKernel.PicardCommutative.Construction.characterPicardFppfKernelIso A B f.hom).hom
      (kernel.ι (AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback A B f.hom))).symm)

end AlgebraicGeometry.Isogenies.NeighborCounting.Field.PicardPresentation.Surjectivity

namespace AlgebraicGeometry.Isogenies.NeighborCounting.Field.PicardPresentation

/-! The actual character subgroup in the known dual presents the
quotient's Picard sheaf as its categorical cokernel. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] {d : ℕ}
variable {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A)

def isogenyCharacterGroupInclusion : (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).dual ⟶ Grp.mk D.abelian.scheme := by
  have : IsMonHom (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion D f) := CharacterKernelQuotient.fieldCharacterInclusion_isMonHom D f
  exact Grp.homMk (A := (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).dual) (B := Grp.mk D.abelian.scheme)
    (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion D f)

def isogenyCharacterSheafInclusion :
    @AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).dual (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).commutative ⟶
      AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk D.abelian.scheme) := by
  have : IsCommMonObj (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).dual.X := (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).commutative
  exact AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (isogenyCharacterGroupInclusion D f)

theorem isogenyCharacterSheafInclusion_mono : Mono (isogenyCharacterSheafInclusion D f) := by
  have : IsCommMonObj (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).dual.X := (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).commutative
  have : IsClosedImmersion (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion D f).left := AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion_closed D f
  have : Mono (isogenyCharacterGroupInclusion D f).hom.hom :=
    Over.mono_of_mono_left (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion D f)
  exact AbelianScheme.CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono (isogenyCharacterGroupInclusion D f)

def isogenyPicardProjection : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk D.abelian.scheme) ⟶
    AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.homogeneousPicardFppfAb B :=
  (ReducedPicardSheafRepresentation.originalDualPicardSheafIso D).hom ≫ AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback B A f.hom

theorem isogenyPicardProjection_apply (T : Over (Spec (.of k))) (x : T ⟶ D.abelian.scheme) :
    (isogenyPicardProjection D f).hom.app (.op T) (ULift.up x) =
      (Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullback B A f.hom).hom.app (.op T) (D.representable.homEquiv x) :=
  AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback_apply B A f.hom T (D.representable.homEquiv x)

theorem isogenyPicardProjection_zero :
    isogenyCharacterSheafInclusion D f ≫ isogenyPicardProjection D f = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨x⟩
  exact (isogenyPicardProjection_apply D f T.unop (x ≫ AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion D f)).trans
    ((AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion_pullback D f T.unop x).trans
      (Picard.Homomorphisms.HomogeneousGroup.Construction.trivialHomogeneousPicardClass_eq_one B T.unop))

def isogenyPicardProjection_isKernel :
    IsLimit (KernelFork.ofι (isogenyCharacterSheafInclusion D f) (isogenyPicardProjection_zero D f)) := by
  have : LocallyOfFinitePresentation f.hom.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType (by rw [f.hom.w]; infer_instance) inferInstance
  have : Mono (isogenyCharacterSheafInclusion D f) := isogenyCharacterSheafInclusion_mono D f
  refine AbelianScheme.CartierDuality.SheafKernels.Construction.Schemes.sheafKernelIsLimitOfPoints (isogenyCharacterSheafInclusion D f)
    (isogenyPicardProjection D f) (isogenyPicardProjection_zero D f) ?_
  intro T x hx
  obtain ⟨x⟩ := x
  have hc : (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback B.scheme A.scheme f.hom).hom.app (.op T)
      (D.representable.homEquiv x) = Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass B.scheme T :=
    ((isogenyPicardProjection_apply D f T x).symm.trans hx).trans
      (Picard.Homomorphisms.HomogeneousGroup.Construction.trivialHomogeneousPicardClass_eq_one B T).symm
  obtain ⟨χ, hχ, _⟩ := AbelianScheme.FrobeniusKernel.PicardExactness.Construction.picardPullback_kernel_character_unique f.hom T (D.representable.homEquiv x) hc
  let y := ((AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).sectionEquiv T).symm χ
  have hy : (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).sectionEquiv T y = χ :=
    ((AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).sectionEquiv T).apply_symm_apply χ
  have he : y ≫ AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion D f = x := D.representable.homEquiv.injective
    ((AbelianScheme.CartierDuality.PicardMonomorphism.Construction.KernelCharacters.cartierToPicard_representation f.hom (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D)
      (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f) T y).trans
        ((congrArg (AbelianScheme.CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f.hom T) hy).trans hχ))
  exact ⟨ULift.up y, congrArg ULift.up he⟩

theorem isogenyPicardProjection_epi (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) : Epi (isogenyPicardProjection D f) :=
  epi_comp' inferInstance (Surjectivity.picardPullback_epi_with_return_isogeny D r f)

def isogenyPicardProjection_isCokernel (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) :
    IsColimit (CokernelCofork.ofπ (isogenyPicardProjection D f) (isogenyPicardProjection_zero D f)) := by
  have : Epi (isogenyPicardProjection D f) := isogenyPicardProjection_epi D f r
  exact AbelianScheme.CartierDuality.QuotientRepresentability.Construction.Exactness.cokernelOfKernelEpi _ _ _ (isogenyPicardProjection_isKernel D f)

def isogenyPicardCokernelIso (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) :
    cokernel (isogenyCharacterSheafInclusion D f) ≅ AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.homogeneousPicardFppfAb B :=
  (colimit.isColimit (parallelPair (isogenyCharacterSheafInclusion D f) 0)).coconePointUniqueUpToIso
    (isogenyPicardProjection_isCokernel D f r)

end AlgebraicGeometry.Isogenies.NeighborCounting.Field.PicardPresentation

end

end OAI
