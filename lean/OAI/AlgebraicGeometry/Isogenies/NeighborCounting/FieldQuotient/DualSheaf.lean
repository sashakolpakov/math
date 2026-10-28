import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.PicardPresentation
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

/-! # Dual Sheaf -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf.Representation

/-! The concrete quotient of the known dual represents the quotient
abelian variety's actual Picard sheaf, with the original group law. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.PicardPresentation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient

variable {k : Type} [Field k] {d : ℕ}
variable {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

def quotientDualPicardSheafIso :
    AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme) ≅
      AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.homogeneousPicardFppfAb B := by
  have : IsCommMonObj (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).dual.X := (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).commutative
  have : IsMonHom (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion D f) := NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterInclusion_isMonHom D f
  have : IsClosedImmersion (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion D f).left := AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion_closed D f
  have : Mono (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion D f) := Over.mono_of_mono_left _
  exact (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).commutativeSheafCokernelIso.symm ≪≫ NeighborCounting.Field.PicardPresentation.isogenyPicardCokernelIso D f r

def quotientDualPicardPoints (T : Over (Spec (.of k))) :
    (T ⟶ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme) ≃* B.homogeneousPicardSheaf.obj.obj (.op T) :=
  MulEquiv.ulift.symm.trans
    (((sheafToPresheaf (Scheme.fppfTopology.over (Spec (.of k))) CommGrpCat).mapIso
      (quotientDualPicardSheafIso D f r)).app (.op T)).commGroupIsoToMulEquiv

theorem quotientDualPicardPoints_natural {T U : Over (Spec (.of k))} (t : U ⟶ T)
    (x : T ⟶ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme) :
    quotientDualPicardPoints D f r U (t ≫ x) =
      B.homogeneousPicardSheaf.obj.map t.op (quotientDualPicardPoints D f r T x) := by
  have hn := (quotientDualPicardSheafIso D f r).hom.hom.naturality_apply t.op (ULift.up x)
  exact hn.trans (Picard.Homomorphisms.GroupSheafMaps.Construction.picardTypeSheafifyRestrictHom_apply (Picard.Homomorphisms.HomogeneousGroup.Construction.homogeneousPicardGroupPresheaf B) t.op
    (quotientDualPicardPoints D f r T x))

def quotientDualRepresentable :
    B.homogeneousPicardSheaf.obj.RepresentableBy (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme where
  homEquiv := (quotientDualPicardPoints D f r _).toEquiv
  homEquiv_comp t x := quotientDualPicardPoints_natural D f r t x

theorem quotientDualRepresentable_origin (T : Over (Spec (.of k))) :
    (quotientDualRepresentable D f r).homEquiv (1 : T ⟶ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme) =
      B.trivialHomogeneousPicardClass T :=
  (quotientDualPicardPoints D f r T).map_one.trans (Picard.Homomorphisms.HomogeneousGroup.Construction.trivialHomogeneousPicardClass_eq_one B T).symm

end AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf.Representation

namespace AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf.Representation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.PicardPresentation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient
section

/-! The constructed Picard representation pulls back along the actual
quotient projection to the original complementary-isogeny pullback. -/

variable {k : Type} [Field k] {d : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

theorem quotientDualPicardSheafIso_projection :
    (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).commutativeSheafProjection ≫ (Representation.quotientDualPicardSheafIso D f r).hom =
      NeighborCounting.Field.PicardPresentation.isogenyPicardProjection D f := by
  have : IsCommMonObj (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).dual.X := (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyKernelCharacters f).commutative
  have : IsMonHom (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion D f) := NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterInclusion_isMonHom D f
  have : IsClosedImmersion (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion D f).left := AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion_closed D f
  have : Mono (AbelianScheme.FrobeniusKernel.CharacterQuotient.Construction.isogenyCharacterInclusion D f) := Over.mono_of_mono_left _
  let Q := NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f
  have hQ : Q.commutativeSheafProjection ≫ Q.commutativeSheafCokernelIso.inv =
      cokernel.π (NeighborCounting.Field.PicardPresentation.isogenyCharacterSheafInclusion D f) :=
    IsColimit.comp_coconePointUniqueUpToIso_inv
      (colimit.isColimit (parallelPair (NeighborCounting.Field.PicardPresentation.isogenyCharacterSheafInclusion D f) 0))
      Q.commutativeSheafProjection_isCokernel WalkingParallelPair.one
  have hP : cokernel.π (NeighborCounting.Field.PicardPresentation.isogenyCharacterSheafInclusion D f) ≫ (NeighborCounting.Field.PicardPresentation.isogenyPicardCokernelIso D f r).hom =
      NeighborCounting.Field.PicardPresentation.isogenyPicardProjection D f :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit (parallelPair (NeighborCounting.Field.PicardPresentation.isogenyCharacterSheafInclusion D f) 0))
      (NeighborCounting.Field.PicardPresentation.isogenyPicardProjection_isCokernel D f r) WalkingParallelPair.one
  exact (Category.assoc Q.commutativeSheafProjection Q.commutativeSheafCokernelIso.inv
      (NeighborCounting.Field.PicardPresentation.isogenyPicardCokernelIso D f r).hom).symm.trans
    ((congrArg (fun a => a ≫ (NeighborCounting.Field.PicardPresentation.isogenyPicardCokernelIso D f r).hom) hQ).trans hP)

theorem quotientDualRepresentable_projection (T : Over (Spec (.of k))) (x : T ⟶ D.abelian.scheme) :
    (Representation.quotientDualRepresentable D f r).homEquiv (x ≫ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection) =
      (Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullback B A f.hom).hom.app (.op T) (D.representable.homEquiv x) := by
  have hx := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg
      (fun z : AbelianScheme.CartierDuality.CommutativeSheavesAb.Construction.Schemes.representedFppfAb (Spec (.of k)) (Grp.mk D.abelian.scheme) ⟶ AbelianScheme.FrobeniusKernel.PicardCommutativeSheaf.Construction.homogeneousPicardFppfAb B => z.hom)
      (quotientDualPicardSheafIso_projection D f r)) (.op T)) (ULift.up x)
  exact hx.trans (NeighborCounting.Field.PicardPresentation.isogenyPicardProjection_apply D f T x)

end

/-! The pulled-back original Poincare line is a normalized actual line
representing the quotient-dual universal class on the finite cover. -/

open _root_.CategoryTheory.MonoidalCategory

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {k : Type} [Field k] {d : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

def quotientDualSourcePoincare : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (D.abelian.scheme ⊗ B.scheme).left :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (D.abelian.scheme ◁ f.hom).left D.poincare

theorem quotientDualSourcePoincare_homogeneous :
    B.IsHomogeneousPicardClass D.abelian.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualSourcePoincare D f)) :=
  Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardClass_pullback B A f.hom D.poincareHomogeneous

theorem quotientDualSourcePoincare_normalized :
    PoincareNormalization.IsNormalized B D.abelian.scheme (quotientDualSourcePoincare D f) :=
  PoincareNormalization.abelianPull_normalized D f.hom

theorem quotientDualSourcePoincare_class :
    (Representation.quotientDualRepresentable D f r).homEquiv (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection =
      (toSheafify (Scheme.fppfTopology.over (Spec (.of k))) B.homogeneousPicardPresheaf).app
        (.op D.abelian.scheme)
        ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualSourcePoincare D f), quotientDualSourcePoincare_homogeneous D f⟩ := by
  have hp := quotientDualRepresentable_projection D f r D.abelian.scheme (𝟙 D.abelian.scheme)
  have hu := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality (Scheme.fppfTopology.over (Spec (.of k)))
      (Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullbackPresheaf B A f.hom)) (.op D.abelian.scheme))
      ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf D.poincare, D.poincareHomogeneous⟩
  exact (congrArg (Representation.quotientDualRepresentable D f r).homEquiv
      (Category.id_comp (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection)).symm.trans
    (hp.trans ((congrArg ((Picard.Homomorphisms.HomogeneousPullback.Construction.homogeneousPicardPullback B A f.hom).hom.app (.op D.abelian.scheme))
      D.universalClass).trans hu.symm))

end AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf

end

end OAI
