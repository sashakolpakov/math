import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CharacterQuotient
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.PicardIsogenySurjectivity
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.GeometricQuotientSheafCokernel

/-! # Quotient Dual Is -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualIs.Construction

noncomputable section

section

/-! The actual character subgroup in the known dual presents the
quotient's Picard sheaf as its categorical cokernel. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {d h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A)

def isogenyCharacterGroupInclusion : (CharacterQuotient.Construction.isogenyKernelCharacters f).dual ⟶ Grp.mk D.abelian.scheme := by
  have : IsMonHom (CharacterQuotient.Construction.isogenyCharacterInclusion D f) := CharacterQuotient.Construction.isogenyCharacterInclusion_isMonHom D f
  exact Grp.homMk (A := (CharacterQuotient.Construction.isogenyKernelCharacters f).dual) (B := Grp.mk D.abelian.scheme)
    (CharacterQuotient.Construction.isogenyCharacterInclusion D f)

def isogenyCharacterSheafInclusion :
    @CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (CharacterQuotient.Construction.isogenyKernelCharacters f).dual (CharacterQuotient.Construction.isogenyKernelCharacters f).commutative ⟶
      CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk D.abelian.scheme) := by
  have : IsCommMonObj (CharacterQuotient.Construction.isogenyKernelCharacters f).dual.X := (CharacterQuotient.Construction.isogenyKernelCharacters f).commutative
  exact CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap (isogenyCharacterGroupInclusion D f)

theorem isogenyCharacterSheafInclusion_mono : Mono (isogenyCharacterSheafInclusion D f) := by
  have : IsCommMonObj (CharacterQuotient.Construction.isogenyKernelCharacters f).dual.X := (CharacterQuotient.Construction.isogenyKernelCharacters f).commutative
  have : IsClosedImmersion (CharacterQuotient.Construction.isogenyCharacterInclusion D f).left := CharacterQuotient.Construction.isogenyCharacterInclusion_closed D f
  have : Mono (isogenyCharacterGroupInclusion D f).hom.hom :=
    Over.mono_of_mono_left (CharacterQuotient.Construction.isogenyCharacterInclusion D f)
  exact CartierDuality.RepresentedMorphisms.Construction.Schemes.representedFppfAbMap_mono (isogenyCharacterGroupInclusion D f)

def isogenyPicardProjection : CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk D.abelian.scheme) ⟶
    PicardCommutativeSheaf.Construction.homogeneousPicardFppfAb B :=
  (PicardSheafRepresentation.Construction.originalDualPicardSheafIso D).hom ≫ PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback B A f.hom

theorem isogenyPicardProjection_apply (T : Over (Spec (.of k))) (x : T ⟶ D.abelian.scheme) :
    (isogenyPicardProjection D f).hom.app (.op T) (ULift.up x) =
      (Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullback B A f.hom).hom.app (.op T) (D.representable.homEquiv x) :=
  PicardCommutativeSheaf.Construction.homogeneousPicardFppfPullback_apply B A f.hom T (D.representable.homEquiv x)

theorem isogenyPicardProjection_zero :
    isogenyCharacterSheafInclusion D f ≫ isogenyPicardProjection D f = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext T
  apply CommGrpCat.hom_ext
  apply MonoidHom.ext
  rintro ⟨x⟩
  exact (isogenyPicardProjection_apply D f T.unop (x ≫ CharacterQuotient.Construction.isogenyCharacterInclusion D f)).trans
    ((CharacterQuotient.Construction.isogenyCharacterInclusion_pullback D f T.unop x).trans
      (Picard.Homomorphisms.HomogeneousGroup.Construction.trivialHomogeneousPicardClass_eq_one B T.unop))

def isogenyPicardProjection_isKernel :
    IsLimit (KernelFork.ofι (isogenyCharacterSheafInclusion D f) (isogenyPicardProjection_zero D f)) := by
  have : LocallyOfFinitePresentation f.hom.left :=
    Picard.Homomorphisms.FinitePresentation.Construction.locallyOfFinitePresentation_of_comp_of_finiteType (by rw [f.hom.w]; infer_instance) inferInstance
  have : Mono (isogenyCharacterSheafInclusion D f) := isogenyCharacterSheafInclusion_mono D f
  refine CartierDuality.SheafKernels.Construction.Schemes.sheafKernelIsLimitOfPoints (isogenyCharacterSheafInclusion D f)
    (isogenyPicardProjection D f) (isogenyPicardProjection_zero D f) ?_
  intro T x hx
  obtain ⟨x⟩ := x
  have hc : (Picard.Homomorphisms.UnbundledHomogeneousPullback.Construction.UnbundledPicard.homogeneousPicardPullback B.scheme A.scheme f.hom).hom.app (.op T)
      (D.representable.homEquiv x) = Picard.Homomorphisms.UnbundledHomogeneous.Construction.UnbundledPicard.trivialHomogeneousPicardClass B.scheme T :=
    ((isogenyPicardProjection_apply D f T x).symm.trans hx).trans
      (Picard.Homomorphisms.HomogeneousGroup.Construction.trivialHomogeneousPicardClass_eq_one B T).symm
  obtain ⟨χ, hχ, _⟩ := PicardExactness.Construction.picardPullback_kernel_character_unique f.hom T (D.representable.homEquiv x) hc
  let y := ((CharacterQuotient.Construction.isogenyKernelCharacters f).sectionEquiv T).symm χ
  have hy : (CharacterQuotient.Construction.isogenyKernelCharacters f).sectionEquiv T y = χ :=
    ((CharacterQuotient.Construction.isogenyKernelCharacters f).sectionEquiv T).apply_symm_apply χ
  have he : y ≫ CharacterQuotient.Construction.isogenyCharacterInclusion D f = x := D.representable.homEquiv.injective
    ((CartierDuality.PicardMonomorphism.Construction.KernelCharacters.cartierToPicard_representation f.hom (Picard.Homomorphisms.UnbundledDualData.Construction.UnbundledPicard.DualData.ofBundled D)
      (CharacterQuotient.Construction.isogenyKernelCharacters f) T y).trans
        ((congrArg (CartierDuality.ParameterizedCharacterProducts.Construction.KernelCharacters.parameterCharacterPicardHom f.hom T) hy).trans hχ))
  exact ⟨ULift.up y, congrArg ULift.up he⟩

theorem isogenyPicardProjection_epi (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) : Epi (isogenyPicardProjection D f) :=
  epi_comp' inferInstance (PicardIsogenySurjectivity.Construction.picardPullback_epi_with_return_isogeny D r f)

def isogenyPicardProjection_isCokernel (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) :
    IsColimit (CokernelCofork.ofπ (isogenyPicardProjection D f) (isogenyPicardProjection_zero D f)) := by
  have : Epi (isogenyPicardProjection D f) := isogenyPicardProjection_epi D f r
  exact CartierDuality.QuotientRepresentability.Construction.Exactness.cokernelOfKernelEpi _ _ _ (isogenyPicardProjection_isKernel D f)

def isogenyPicardCokernelIso (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B) :
    cokernel (isogenyCharacterSheafInclusion D f) ≅ PicardCommutativeSheaf.Construction.homogeneousPicardFppfAb B :=
  (colimit.isColimit (parallelPair (isogenyCharacterSheafInclusion D f) 0)).coconePointUniqueUpToIso
    (isogenyPicardProjection_isCokernel D f r)

end

section

/-! The concrete quotient of the known dual represents the quotient
abelian variety's actual Picard sheaf, with the original group law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {d h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

def quotientDualPicardSheafIso :
    CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk (CharacterQuotient.Construction.isogenyCharacterQuotient D f).abelian.scheme) ≅
      PicardCommutativeSheaf.Construction.homogeneousPicardFppfAb B := by
  have : IsCommMonObj (CharacterQuotient.Construction.isogenyKernelCharacters f).dual.X := (CharacterQuotient.Construction.isogenyKernelCharacters f).commutative
  have : IsMonHom (CharacterQuotient.Construction.isogenyCharacterInclusion D f) := CharacterQuotient.Construction.isogenyCharacterInclusion_isMonHom D f
  have : IsClosedImmersion (CharacterQuotient.Construction.isogenyCharacterInclusion D f).left := CharacterQuotient.Construction.isogenyCharacterInclusion_closed D f
  have : Mono (CharacterQuotient.Construction.isogenyCharacterInclusion D f) := Over.mono_of_mono_left _
  exact (CharacterQuotient.Construction.isogenyCharacterQuotient D f).commutativeSheafCokernelIso.symm ≪≫ isogenyPicardCokernelIso D f r

def quotientDualPicardPoints (T : Over (Spec (.of k))) :
    (T ⟶ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).abelian.scheme) ≃* B.homogeneousPicardSheaf.obj.obj (.op T) :=
  MulEquiv.ulift.symm.trans
    (((sheafToPresheaf (Scheme.fppfTopology.over (Spec (.of k))) CommGrpCat).mapIso
      (quotientDualPicardSheafIso D f r)).app (.op T)).commGroupIsoToMulEquiv

theorem quotientDualPicardPoints_natural {T U : Over (Spec (.of k))} (t : U ⟶ T)
    (x : T ⟶ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).abelian.scheme) :
    quotientDualPicardPoints D f r U (t ≫ x) =
      B.homogeneousPicardSheaf.obj.map t.op (quotientDualPicardPoints D f r T x) := by
  have hn := (quotientDualPicardSheafIso D f r).hom.hom.naturality_apply t.op (ULift.up x)
  exact hn.trans (Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom_apply (Picard.Homomorphisms.HomogeneousGroup.Construction.homogeneousPicardGroupPresheaf B) t.op
    (quotientDualPicardPoints D f r T x))

def quotientDualRepresentable :
    B.homogeneousPicardSheaf.obj.RepresentableBy (CharacterQuotient.Construction.isogenyCharacterQuotient D f).abelian.scheme where
  homEquiv := (quotientDualPicardPoints D f r _).toEquiv
  homEquiv_comp t x := quotientDualPicardPoints_natural D f r t x

theorem quotientDualRepresentable_origin (T : Over (Spec (.of k))) :
    (quotientDualRepresentable D f r).homEquiv (1 : T ⟶ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).abelian.scheme) =
      B.trivialHomogeneousPicardClass T :=
  (quotientDualPicardPoints D f r T).map_one.trans (Picard.Homomorphisms.HomogeneousGroup.Construction.trivialHomogeneousPicardClass_eq_one B T).symm

end

/-! The constructed Picard representation pulls back along the actual
quotient projection to the original complementary-isogeny pullback. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {k : Type} [Field k] [IsAlgClosed k] {d h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

theorem quotientDualPicardSheafIso_projection :
    (CharacterQuotient.Construction.isogenyCharacterQuotient D f).commutativeSheafProjection ≫ (quotientDualPicardSheafIso D f r).hom =
      isogenyPicardProjection D f := by
  have : IsCommMonObj (CharacterQuotient.Construction.isogenyKernelCharacters f).dual.X := (CharacterQuotient.Construction.isogenyKernelCharacters f).commutative
  have : IsMonHom (CharacterQuotient.Construction.isogenyCharacterInclusion D f) := CharacterQuotient.Construction.isogenyCharacterInclusion_isMonHom D f
  have : IsClosedImmersion (CharacterQuotient.Construction.isogenyCharacterInclusion D f).left := CharacterQuotient.Construction.isogenyCharacterInclusion_closed D f
  have : Mono (CharacterQuotient.Construction.isogenyCharacterInclusion D f) := Over.mono_of_mono_left _
  let Q := CharacterQuotient.Construction.isogenyCharacterQuotient D f
  have hQ : Q.commutativeSheafProjection ≫ Q.commutativeSheafCokernelIso.inv =
      cokernel.π (isogenyCharacterSheafInclusion D f) :=
    IsColimit.comp_coconePointUniqueUpToIso_inv
      (colimit.isColimit (parallelPair (isogenyCharacterSheafInclusion D f) 0))
      Q.commutativeSheafProjection_isCokernel WalkingParallelPair.one
  have hP : cokernel.π (isogenyCharacterSheafInclusion D f) ≫ (isogenyPicardCokernelIso D f r).hom =
      isogenyPicardProjection D f :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (parallelPair (isogenyCharacterSheafInclusion D f) 0))
      (isogenyPicardProjection_isCokernel D f r) WalkingParallelPair.one
  exact (Category.assoc Q.commutativeSheafProjection Q.commutativeSheafCokernelIso.inv
      (isogenyPicardCokernelIso D f r).hom).symm.trans
    ((congrArg (fun a => a ≫ (isogenyPicardCokernelIso D f r).hom) hQ).trans hP)

theorem quotientDualRepresentable_projection (T : Over (Spec (.of k))) (x : T ⟶ D.abelian.scheme) :
    (quotientDualRepresentable D f r).homEquiv (x ≫ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection) =
      (Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullback B A f.hom).hom.app (.op T) (D.representable.homEquiv x) := by
  have hx := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg
      (fun z : CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk D.abelian.scheme) ⟶ PicardCommutativeSheaf.Construction.homogeneousPicardFppfAb B => z.hom)
      (quotientDualPicardSheafIso_projection D f r)) (.op T)) (ULift.up x)
  exact hx.trans (isogenyPicardProjection_apply D f T x)

end

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualIs.Construction
