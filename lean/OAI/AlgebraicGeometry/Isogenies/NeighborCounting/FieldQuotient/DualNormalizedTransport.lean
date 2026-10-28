import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.NormalizedPicardInjection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.RigidifiedUniqueness
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.PicardGlobalFunctions

/-! # Dual Normalized Transport -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualNormalizedTransport

noncomputable section

section

/-! Equal points of the constructed quotient dual give actual normalized
isomorphisms between the corresponding original Poincare families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf.Representation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.PicardPresentation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient

variable {k : Type} [Field k] {d : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
variable (T : Over (Spec (.of k))) (a : T ⟶ D.abelian.scheme)

def quotientDualPoincareFamily : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ B.scheme).left :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (a ▷ B.scheme).left (DualSheaf.quotientDualSourcePoincare D f)

theorem quotientDualPoincareFamily_homogeneous :
    B.IsHomogeneousPicardClass T (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualPoincareFamily D f T a)) :=
  (DualSheaf.quotientDualSourcePoincare_homogeneous D f).pullback B a

def quotientDualPoincareFamily_zeroIso :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (PoincareNormalization.familyZero B T).left (quotientDualPoincareFamily D f T a)).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left :=
  PoincareNormalization.familyPullbackZeroIso B a (DualSheaf.quotientDualSourcePoincare D f)
    (DualSheaf.quotientDualSourcePoincare_normalized D f).some

theorem quotientDualPoincareFamily_class :
    (DualSheaf.Representation.quotientDualRepresentable D f r).homEquiv (a ≫ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection) =
      (toSheafify (Scheme.fppfTopology.over (Spec (.of k))) B.homogeneousPicardPresheaf).app (.op T)
        ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualPoincareFamily D f T a), quotientDualPoincareFamily_homogeneous D f T a⟩ := by
  have hn := (toSheafify (Scheme.fppfTopology.over (Spec (.of k))) B.homogeneousPicardPresheaf).naturality_apply a.op
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (DualSheaf.quotientDualSourcePoincare D f), DualSheaf.quotientDualSourcePoincare_homogeneous D f⟩
  exact ((DualSheaf.Representation.quotientDualRepresentable D f r).homEquiv_comp a (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection).trans
    ((congrArg (B.homogeneousPicardSheaf.obj.map a.op) (DualSheaf.quotientDualSourcePoincare_class D f r)).trans hn.symm)

include r in
theorem quotientDualPoincareFamily_relativeClass_eq (b : T ⟶ D.abelian.scheme)
    (hab : a ≫ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection = b ≫ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B.scheme).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualPoincareFamily D f T a)) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B.scheme).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualPoincareFamily D f T b)) := by
  have hc := (quotientDualPoincareFamily_class D f r T a).symm.trans
    ((congrArg (DualSheaf.Representation.quotientDualRepresentable D f r).homEquiv hab).trans
      (quotientDualPoincareFamily_class D f r T b))
  have ha := ConcreteCategory.congr_hom
    (NatTrans.congr_app (Picard.Homomorphisms.PoincareDetection.Construction.homogeneousPicardSheafInclusion_toSheafify B) (.op T))
      ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualPoincareFamily D f T a), quotientDualPoincareFamily_homogeneous D f T a⟩
  have hb := ConcreteCategory.congr_hom
    (NatTrans.congr_app (Picard.Homomorphisms.PoincareDetection.Construction.homogeneousPicardSheafInclusion_toSheafify B) (.op T))
      ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualPoincareFamily D f T b), quotientDualPoincareFamily_homogeneous D f T b⟩
  exact ha.symm.trans ((congrArg (B.homogeneousPicardSheafInclusion.hom.app (.op T)) hc).trans hb)

include r in
theorem quotientDualPoincareFamily_normalizedIso_exists [CompactSpace T.left] [QuasiSeparatedSpace T.left]
    (b : T ⟶ D.abelian.scheme)
    (hab : a ≫ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection = b ≫ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection) :
    ∃ e : (quotientDualPoincareFamily D f T a).sheaf ≅ (quotientDualPoincareFamily D f T b).sheaf,
      (Scheme.Modules.pullback (PoincareNormalization.familyZero B T).left).map e.hom ≫
        (quotientDualPoincareFamily_zeroIso D f T b).hom = (quotientDualPoincareFamily_zeroIso D f T a).hom :=
  NeighborCounting.Field.NormalizedPicardInjection.normalized_iso_of_picard_eq B
    (quotientDualPoincareFamily D f T a) (quotientDualPoincareFamily D f T b)
    (quotientDualPoincareFamily_zeroIso D f T a) (quotientDualPoincareFamily_zeroIso D f T b)
    (quotientDualPoincareFamily_relativeClass_eq D f r T a b hab)

end

/-! The normalized Poincare family comparisons have the actual unit
and composition laws, by uniqueness of zero-preserving isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf.Representation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.PicardPresentation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient

variable {k : Type} [Field k] {d : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
variable (T : Over (Spec (.of k))) (a b : T ⟶ D.abelian.scheme)

theorem quotientDualPoincareIso_ext
    (e e' : (quotientDualPoincareFamily D f T a).sheaf ≅ (quotientDualPoincareFamily D f T b).sheaf)
    (he : (Scheme.Modules.pullback (PoincareNormalization.familyZero B T).left).map e.hom ≫
      (quotientDualPoincareFamily_zeroIso D f T b).hom = (quotientDualPoincareFamily_zeroIso D f T a).hom)
    (he' : (Scheme.Modules.pullback (PoincareNormalization.familyZero B T).left).map e'.hom ≫
      (quotientDualPoincareFamily_zeroIso D f T b).hom = (quotientDualPoincareFamily_zeroIso D f T a).hom) : e = e' := by
  have : IsIso (fst T B.scheme).left.appTop :=
    NeighborCounting.Field.PicardGlobalFunctions.abelian_product_app_isIso B T ⊤
  exact PELModuli.IntegralModel.Picard.RigidifiedUniqueness.PicardRigidifiedUniqueness.normalizedIso_unique
    (fst T B.scheme).left (PoincareNormalization.familyZero B T).left (PoincareNormalization.familyZero_projection B T)
    (ConcreteCategory.bijective_of_isIso (fst T B.scheme).left.appTop).surjective
    (quotientDualPoincareFamily D f T a).locallyTrivial
    (quotientDualPoincareFamily_zeroIso D f T a) (quotientDualPoincareFamily_zeroIso D f T b) e e' he he'

variable [CompactSpace T.left] [QuasiSeparatedSpace T.left]
variable (hab : a ≫ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection = b ≫ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection)

def quotientDualNormalizedIso :
    (quotientDualPoincareFamily D f T a).sheaf ≅ (quotientDualPoincareFamily D f T b).sheaf :=
  (quotientDualPoincareFamily_normalizedIso_exists D f r T a b hab).choose

theorem quotientDualNormalizedIso_zero :
    (Scheme.Modules.pullback (PoincareNormalization.familyZero B T).left).map (quotientDualNormalizedIso D f r T a b hab).hom ≫
      (quotientDualPoincareFamily_zeroIso D f T b).hom = (quotientDualPoincareFamily_zeroIso D f T a).hom :=
  (quotientDualPoincareFamily_normalizedIso_exists D f r T a b hab).choose_spec

theorem quotientDualNormalizedIso_self : quotientDualNormalizedIso D f r T a a rfl = Iso.refl _ := by
  apply quotientDualPoincareIso_ext D f T a a
  · exact quotientDualNormalizedIso_zero D f r T a a rfl
  · exact (congrArg (fun m => m ≫ (quotientDualPoincareFamily_zeroIso D f T a).hom)
      ((Scheme.Modules.pullback (PoincareNormalization.familyZero B T).left).map_id (quotientDualPoincareFamily D f T a).sheaf)).trans
        (Category.id_comp _)

theorem quotientDualNormalizedIso_comp (c : T ⟶ D.abelian.scheme)
    (hbc : b ≫ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection = c ≫ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection) :
    quotientDualNormalizedIso D f r T a b hab ≪≫ quotientDualNormalizedIso D f r T b c hbc =
      quotientDualNormalizedIso D f r T a c (hab.trans hbc) := by
  apply quotientDualPoincareIso_ext D f T a c
  · let F := Scheme.Modules.pullback (PoincareNormalization.familyZero B T).left
    let e₁ := quotientDualNormalizedIso D f r T a b hab
    let e₂ := quotientDualNormalizedIso D f r T b c hbc
    exact (congrArg (fun m => m ≫ (quotientDualPoincareFamily_zeroIso D f T c).hom)
      (F.map_comp e₁.hom e₂.hom)).trans
        ((Category.assoc (F.map e₁.hom) (F.map e₂.hom)
          (quotientDualPoincareFamily_zeroIso D f T c).hom).trans
          ((congrArg (fun m => F.map e₁.hom ≫ m) (quotientDualNormalizedIso_zero D f r T b c hbc)).trans
            (quotientDualNormalizedIso_zero D f r T a b hab)))
  · exact quotientDualNormalizedIso_zero D f r T a c (hab.trans hbc)

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualNormalizedTransport
