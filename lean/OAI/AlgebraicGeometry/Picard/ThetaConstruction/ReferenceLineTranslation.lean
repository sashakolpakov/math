import OAI.AlgebraicGeometry.Picard.ThetaConstruction.RelativeDifferenceEq
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Picard.BaseTwists
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.BaseChange

/-! # Reference Line Translation -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceLineTranslation.Geometric

noncomputable section

section

/-! The normalized difference zero condition is translation invariance
of the original line, over an arbitrary original base. Normalization
changes the total-family line only by a line from the test base. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {S : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) {U : Over S}

theorem translationInvariant_congr_relativeClass (a : U ⟶ A.scheme)
    (q r : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ A.scheme).left)
    (h : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) q = (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U) r) :
    A.TranslationInvariant a q ↔ A.TranslationInvariant a r := by
  have ht := RelativeTranslationClasses.Geometric.translation_relativeClass_congr A a q r h
  exact ⟨fun hq => ht.symm.trans (hq.trans h), fun hr => ht.trans (hr.trans h.symm)⟩

theorem originalLineFamily_picard_normalization (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (U : Over S) :
    (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((RelativeDifferenceBundle.Geometric.identityNormalizedLine A L).pullback (snd U A.scheme).left)) =
        (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op U)
          (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd U A.scheme).left)) := by
  let relativeMap : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ A.scheme).left →* AbelianModuli.HilbertConstruction.Picard.PicardSheaf.PicardSections A.scheme U :=
    Homomorphisms.RelativeGroup.Construction.toRelativePicardHom A.scheme U
  let B := L.pullback η[A.scheme].left
  have hs : (snd U A.scheme).left ≫ A.scheme.hom = (fst U A.scheme).left ≫ U.hom :=
    CategoryTheory.Limits.pullback.condition.symm
  have hb : relativeMap (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (fst U A.scheme).left (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback U.hom (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B))) = 1 :=
    (AbelianModuli.HilbertConstruction.Picard.BaseBundleTriviality.baseBundle_relativePicardClass_trivial A.scheme U (B.pullback U.hom)).trans
      (Homomorphisms.RelativeGroup.Construction.trivialPicardClass_eq_one A.scheme U)
  change relativeMap (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd U A.scheme).left
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L * (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback A.scheme.hom (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf B))⁻¹)) =
      relativeMap (RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback (snd U A.scheme).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))
  rw [map_mul, map_inv, RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp, hs, ← RepresentationTheory.Theta.Geometric.Picard.PicardPullback.picardPullback_comp,
    map_mul, map_inv, hb, inv_one, mul_one]

theorem relativeDifference_zero_iff_originalTranslation
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) (a : U ⟶ A.scheme) :
    (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue a = AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A.scheme U ↔
      A.TranslationInvariant a (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd U A.scheme).left)) :=
  (RelativeDifferenceEq.Geometric.relativeRigidifiedDifference_zero_iff_translation A L a).trans
    (translationInvariant_congr_relativeClass A a _ _ (originalLineFamily_picard_normalization A L U))

end

/-! The original-line translation zero condition commutes with any
base change, through the existing relative Picard sheaf comparison and
the actual fiber-product maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

variable {S S' : Scheme} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S) (f : S' ⟶ S) (U : Over S')

theorem translationInvariant_baseChange_iff (a : U ⟶ (A.pullback f).scheme)
    (q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (U ⊗ (A.pullback f).scheme).left) :
    (A.pullback f).TranslationInvariant a q ↔
      A.TranslationInvariant (A.baseChangePointsEquiv f U a)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme f U).inv q) := by
  constructor
  · exact AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.TranslationInvariant.baseChange A f U a q
  · intro h
    apply (AbelianModuli.HilbertConstruction.Homogeneous.BaseChange.picardBaseChangeEquiv A.scheme f U).injective
    exact (AbelianModuli.HilbertConstruction.Picard.BaseChange.toRelativePicard_baseChange_apply A.scheme f U
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass ((A.pullback f).translation a).left q)).trans
        ((congrArg ((AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard A.scheme).app (.op ((Over.map f).obj U)))
          (A.translationClass_baseChange f U a q)).trans
            (h.trans (AbelianModuli.HilbertConstruction.Picard.BaseChange.toRelativePicard_baseChange_apply A.scheme f U q).symm))

theorem originalLineFamily_baseChange_class (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme f U).inv
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((L.pullback (CategoryTheory.Limits.pullback.fst A.scheme.hom f)).pullback
        (snd U (A.pullback f).scheme).left)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd ((Over.map f).obj U) A.scheme).left) := by
  let e : (U ⊗ (A.pullback f).scheme).left ≅ (((Over.map f).obj U) ⊗ A.scheme).left :=
    AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso A.scheme f U
  let p : (A.pullback f).scheme.left ⟶ A.scheme.left := CategoryTheory.Limits.pullback.fst A.scheme.hom f
  have hm : e.hom ≫ (snd ((Over.map f).obj U) A.scheme).left =
      (snd U (A.pullback f).scheme).left ≫ p :=
    AbelianModuli.HilbertConstruction.Picard.BaseChange.familyBaseChangeIso_hom_snd A.scheme f U
  have hi : (e.inv ≫ (snd U (A.pullback f).scheme).left) ≫
      p =
        (snd ((Over.map f).obj U) A.scheme).left := by
    rw [Category.assoc, ← hm, e.inv_hom_id_assoc]
  change AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass e.inv
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (snd U (A.pullback f).scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass p (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L))) = _
  rw [← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, ← AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass_comp, hi]
  rfl

theorem originalTranslation_baseChange_iff (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (a : U ⟶ (A.pullback f).scheme) :
    (A.pullback f).TranslationInvariant a
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf ((L.pullback (CategoryTheory.Limits.pullback.fst A.scheme.hom f)).pullback
        (snd U (A.pullback f).scheme).left)) ↔
      A.TranslationInvariant (A.baseChangePointsEquiv f U a)
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (L.pullback (snd ((Over.map f).obj U) A.scheme).left)) := by
  exact (translationInvariant_baseChange_iff A f U a _).trans
    (iff_of_eq (congrArg (fun q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass (((Over.map f).obj U) ⊗ A.scheme).left =>
      A.TranslationInvariant (A.baseChangePointsEquiv f U a) q)
        (originalLineFamily_baseChange_class A f U L)))

theorem relativeDifference_zero_baseChange_iff (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle A.scheme.left)
    (a : U ⟶ (A.pullback f).scheme) :
    (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference (A.pullback f)
      (L.pullback (CategoryTheory.Limits.pullback.fst A.scheme.hom f))).relativeValue a =
        AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass (A.pullback f).scheme U ↔
      (RelativeDifferenceBundle.Geometric.relativeRigidifiedDifference A L).relativeValue (A.baseChangePointsEquiv f U a) =
        AbelianModuli.HilbertConstruction.Picard.PicardSheaf.trivialPicardClass A.scheme ((Over.map f).obj U) := by
  rw [relativeDifference_zero_iff_originalTranslation, relativeDifference_zero_iff_originalTranslation]
  exact originalTranslation_baseChange_iff A f U L a

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction.ReferenceLineTranslation.Geometric
