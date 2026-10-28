import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualSourcePoincare
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.NormalizedPicardInjection
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.RigidifiedUniqueness

/-! # Quotient Dual Normalized Transport -/

namespace OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualNormalizedTransport.Construction

noncomputable section

section

/-! Equal points of the constructed quotient dual give actual normalized
isomorphisms between the corresponding original Poincare families. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

variable {k : Type} [Field k] [IsAlgClosed k] {d h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
variable (T : Over (Spec (.of k))) (a : T ⟶ D.abelian.scheme)

def quotientDualPoincareFamily : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle (T ⊗ B.scheme).left :=
  AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (a ▷ B.scheme).left (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare D f)

omit [IsAlgClosed k] in
theorem quotientDualPoincareFamily_homogeneous :
    B.IsHomogeneousPicardClass T (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualPoincareFamily D f T a)) :=
  (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare_homogeneous D f).pullback B a

def quotientDualPoincareFamily_zeroIso :
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero B T).left (quotientDualPoincareFamily D f T a)).sheaf ≅
      AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left :=
  Isogenies.NeighborCounting.PoincareNormalization.familyPullbackZeroIso B a (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare D f)
    (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare_normalized D f).some

theorem quotientDualPoincareFamily_class :
    (QuotientDualIs.Construction.quotientDualRepresentable D f r).homEquiv (a ≫ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection) =
      (toSheafify (Scheme.fppfTopology.over (Spec (.of k))) B.homogeneousPicardPresheaf).app (.op T)
        ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualPoincareFamily D f T a), quotientDualPoincareFamily_homogeneous D f T a⟩ := by
  have hn := (toSheafify (Scheme.fppfTopology.over (Spec (.of k))) B.homogeneousPicardPresheaf).naturality_apply a.op
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare D f), QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare_homogeneous D f⟩
  exact ((QuotientDualIs.Construction.quotientDualRepresentable D f r).homEquiv_comp a (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection).trans
    ((congrArg (B.homogeneousPicardSheaf.obj.map a.op) (QuotientDualSourcePoincare.Construction.quotientDualSourcePoincare_class D f r)).trans hn.symm)

include r in
theorem quotientDualPoincareFamily_relativeClass_eq (b : T ⟶ D.abelian.scheme)
    (hab : a ≫ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection = b ≫ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B.scheme).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualPoincareFamily D f T a)) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B.scheme).app (.op T) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualPoincareFamily D f T b)) := by
  have hc := (quotientDualPoincareFamily_class D f r T a).symm.trans
    ((congrArg (QuotientDualIs.Construction.quotientDualRepresentable D f r).homEquiv hab).trans
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
    (hab : a ≫ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection = b ≫ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection) :
    ∃ e : (quotientDualPoincareFamily D f T a).sheaf ≅ (quotientDualPoincareFamily D f T b).sheaf,
      (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero B T).left).map e.hom ≫
        (quotientDualPoincareFamily_zeroIso D f T b).hom = (quotientDualPoincareFamily_zeroIso D f T a).hom :=
  PELModuli.IntegralModel.NormalizedPicardInjection.NormalizedPicard.normalized_iso_of_picard_eq B
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

variable {k : Type} [Field k] [IsAlgClosed k] {d h : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme h (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)
variable (T : Over (Spec (.of k))) (a b : T ⟶ D.abelian.scheme)

theorem quotientDualPoincareIso_ext
    (e e' : (quotientDualPoincareFamily D f T a).sheaf ≅ (quotientDualPoincareFamily D f T b).sheaf)
    (he : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero B T).left).map e.hom ≫
      (quotientDualPoincareFamily_zeroIso D f T b).hom = (quotientDualPoincareFamily_zeroIso D f T a).hom)
    (he' : (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero B T).left).map e'.hom ≫
      (quotientDualPoincareFamily_zeroIso D f T b).hom = (quotientDualPoincareFamily_zeroIso D f T a).hom) : e = e' := by
  have : IsIntegral B.scheme.left := ArithmeticGeometry.OrdinaryLocus.Openness.ConnectedGroupIntegral.Construction.isIntegral_connected_smooth_proper_group B.scheme
  exact PELModuli.IntegralModel.Picard.RigidifiedUniqueness.PicardRigidifiedUniqueness.proper_product_normalizedIso_unique
    T B.scheme (Isogenies.NeighborCounting.PoincareNormalization.familyZero B T).left (Isogenies.NeighborCounting.PoincareNormalization.familyZero_projection B T)
    (quotientDualPoincareFamily D f T a).locallyTrivial
    (quotientDualPoincareFamily_zeroIso D f T a) (quotientDualPoincareFamily_zeroIso D f T b) e e' he he'

variable [CompactSpace T.left] [QuasiSeparatedSpace T.left]
variable (hab : a ≫ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection = b ≫ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection)

def quotientDualNormalizedIso :
    (quotientDualPoincareFamily D f T a).sheaf ≅ (quotientDualPoincareFamily D f T b).sheaf :=
  (quotientDualPoincareFamily_normalizedIso_exists D f r T a b hab).choose

theorem quotientDualNormalizedIso_zero :
    (Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero B T).left).map (quotientDualNormalizedIso D f r T a b hab).hom ≫
      (quotientDualPoincareFamily_zeroIso D f T b).hom = (quotientDualPoincareFamily_zeroIso D f T a).hom :=
  (quotientDualPoincareFamily_normalizedIso_exists D f r T a b hab).choose_spec

theorem quotientDualNormalizedIso_self : quotientDualNormalizedIso D f r T a a rfl = Iso.refl _ := by
  apply quotientDualPoincareIso_ext D f T a a
  · exact quotientDualNormalizedIso_zero D f r T a a rfl
  · exact (congrArg (fun m => m ≫ (quotientDualPoincareFamily_zeroIso D f T a).hom)
      ((Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero B T).left).map_id (quotientDualPoincareFamily D f T a).sheaf)).trans
        (Category.id_comp _)

theorem quotientDualNormalizedIso_comp (c : T ⟶ D.abelian.scheme)
    (hbc : b ≫ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection = c ≫ (CharacterQuotient.Construction.isogenyCharacterQuotient D f).projection) :
    quotientDualNormalizedIso D f r T a b hab ≪≫ quotientDualNormalizedIso D f r T b c hbc =
      quotientDualNormalizedIso D f r T a c (hab.trans hbc) := by
  apply quotientDualPoincareIso_ext D f T a c
  · let F := Scheme.Modules.pullback (Isogenies.NeighborCounting.PoincareNormalization.familyZero B T).left
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

end OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.QuotientDualNormalizedTransport.Construction
