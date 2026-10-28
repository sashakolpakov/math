import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualLinearization
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HomogeneousClassDescent
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv

/-! # Dual At -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualAt

noncomputable section

section

/-! Normalize the actually descended line and identify its class with
the universal point of the constructed quotient-dual representation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization
open OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.Inv.NormalizedPicard

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf.Representation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient

open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.HomogeneousClassDescent.Construction (homogeneousClass_of_fppf_pullback fppfSheaf_restriction_injective)

variable {k : Type} [Field k] {d : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

def quotientDualPoincare : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle ((NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme ⊗ B.scheme).left :=
  (PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass B (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme
    (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (DualLinearization.quotientDualDescendedPoincare D f r))).out

theorem quotientDualPoincare_class : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualPoincare D f r) =
    PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass B (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (DualLinearization.quotientDualDescendedPoincare D f r)) := Quotient.out_eq _

theorem quotientDualPoincare_normalized :
    PoincareNormalization.IsNormalized B (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme (quotientDualPoincare D f r) := by
  apply (PoincareNormalization.normalized_iff_class B _ _).mpr
  exact (congrArg (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (PoincareNormalization.familyZero B (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme).left)
    (quotientDualPoincare_class D f r)).trans
      (PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass_zero B _ (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (DualLinearization.quotientDualDescendedPoincare D f r)))

theorem quotientDualPoincare_pullbackClass :
    AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass (DualCover.quotientDualPoincareCover D f).left (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualPoincare D f r)) =
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (DualSheaf.quotientDualSourcePoincare D f) := by
  have hp : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (DualCover.quotientDualPoincareCover D f).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (DualLinearization.quotientDualDescendedPoincare D f r)) = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (DualSheaf.quotientDualSourcePoincare D f) :=
    Quotient.sound ⟨DualLinearization.quotientDualDescendedPoincare_pullbackIso D f r⟩
  have hs : Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (PoincareNormalization.familyZero B D.abelian.scheme).left
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (DualSheaf.quotientDualSourcePoincare D f)) = 1 :=
    (PoincareNormalization.normalized_iff_class B _ _).mp (DualSheaf.quotientDualSourcePoincare_normalized D f)
  exact (congrArg (Picard.Homomorphisms.SchemePullback.Construction.schemePicardPullback (DualCover.quotientDualPoincareCover D f).left)
    (quotientDualPoincare_class D f r)).trans
      ((PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass_naturality B (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection
        (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (DualLinearization.quotientDualDescendedPoincare D f r))).trans
        ((congrArg (PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass B D.abelian.scheme) hp).trans
          (PELModuli.IntegralModel.Picard.Inv.NormalizedPicard.normalizedClass_eq_self B D.abelian.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (DualSheaf.quotientDualSourcePoincare D f)) hs)))

theorem quotientDualPoincare_homogeneous :
    B.IsHomogeneousPicardClass (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme
      (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualPoincare D f r)) := by
  apply AbelianScheme.FrobeniusKernel.HomogeneousClassDescent.Construction.homogeneousClass_of_fppf_pullback B (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection
  exact Eq.mpr (congrArg (B.IsHomogeneousPicardClass D.abelian.scheme)
    (quotientDualPoincare_pullbackClass D f r)) (DualSheaf.quotientDualSourcePoincare_homogeneous D f)

theorem quotientDualPoincare_universalClass :
    (DualSheaf.Representation.quotientDualRepresentable D f r).homEquiv (𝟙 (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme) =
      (toSheafify (Scheme.fppfTopology.over (Spec (.of k))) B.homogeneousPicardPresheaf).app
        (op (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme)
        ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualPoincare D f r), quotientDualPoincare_homogeneous D f r⟩ := by
  apply AbelianScheme.FrobeniusKernel.HomogeneousClassDescent.Construction.fppfSheaf_restriction_injective B.homogeneousPicardSheaf (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection
  let q := (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterQuotient D f).projection
  let etaPic := toSheafify (Scheme.fppfTopology.over (Spec (.of k))) B.homogeneousPicardPresheaf
  have hleft := ((DualSheaf.Representation.quotientDualRepresentable D f r).homEquiv_comp q (𝟙 _)).symm.trans
    (congrArg (DualSheaf.Representation.quotientDualRepresentable D f r).homEquiv (Category.comp_id q))
  let c0 : B.homogeneousPicardPresheaf.obj (op (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme) :=
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualPoincare D f r), quotientDualPoincare_homogeneous D f r⟩
  let c1 : B.homogeneousPicardPresheaf.obj (op D.abelian.scheme) :=
    ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (DualSheaf.quotientDualSourcePoincare D f), DualSheaf.quotientDualSourcePoincare_homogeneous D f⟩
  have hc : B.homogeneousPicardPresheaf.map q.op c0 = c1 :=
    Subtype.ext (quotientDualPoincare_pullbackClass D f r)
  have hright := (etaPic.naturality_apply q.op c0).symm.trans
    (congrArg (etaPic.app (op D.abelian.scheme)) hc)
  exact hleft.trans ((DualSheaf.quotientDualSourcePoincare_class D f r).trans hright.symm)

theorem quotientDualPoincare_familyClass (T : Over (Spec (.of k)))
    (a : T ⟶ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme) :
    (DualSheaf.Representation.quotientDualRepresentable D f r).homEquiv a =
      (toSheafify (Scheme.fppfTopology.over (Spec (.of k))) B.homogeneousPicardPresheaf).app (op T)
        ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (a ▷ B.scheme).left (quotientDualPoincare D f r)),
          (quotientDualPoincare_homogeneous D f r).pullback B a⟩ := by
  let etaPic := toSheafify (Scheme.fppfTopology.over (Spec (.of k))) B.homogeneousPicardPresheaf
  have h := (DualSheaf.Representation.quotientDualRepresentable D f r).homEquiv_comp a (𝟙 _)
  exact (congrArg (DualSheaf.Representation.quotientDualRepresentable D f r).homEquiv (Category.comp_id a)).symm.trans
    (h.trans ((congrArg (B.homogeneousPicardSheaf.obj.map a.op)
      (quotientDualPoincare_universalClass D f r)).trans
        (etaPic.naturality_apply a.op
          ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf (quotientDualPoincare D f r), quotientDualPoincare_homogeneous D f r⟩).symm))

end

section

/-! The universal class at the quotient identity supplies the second
actual zero-section trivialization of the constructed Poincare line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.PoincareNormalization

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf.Representation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient

variable {k : Type} [Field k] {d : ℕ}
variable {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))} {B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

theorem quotientDualPoincare_normalizedAtDualZero :
    Nonempty ((AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback
      (lift (1 : B.scheme ⟶ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme) (𝟙 B.scheme)).left
      (quotientDualPoincare D f r)).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule B.scheme.left) := by
  have : CompactSpace B.scheme.left := QuasiCompact.compactSpace_of_compactSpace B.scheme.hom
  have : QuasiSeparatedSpace B.scheme.left := quasiSeparatedSpace_of_quasiSeparated B.scheme.hom
  let a : B.scheme ⟶ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme := 1
  let L := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullback (a ▷ B.scheme).left (quotientDualPoincare D f r)
  let M := AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivial (B.scheme ⊗ B.scheme).left
  have hL : PoincareNormalization.IsNormalized B B.scheme L :=
    PoincareNormalization.normalized_family_pullback B a (quotientDualPoincare D f r) (quotientDualPoincare_normalized D f r)
  have hM : PoincareNormalization.IsNormalized B B.scheme M := ⟨AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso (PoincareNormalization.familyZero B B.scheme).left⟩
  have hhom : B.IsHomogeneousPicardClass B.scheme (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) :=
    (quotientDualPoincare_homogeneous D f r).pullback B a
  have hc := (quotientDualPoincare_familyClass D f r B.scheme a).symm.trans
    (DualSheaf.Representation.quotientDualRepresentable_origin D f r B.scheme)
  have hl := ConcreteCategory.congr_hom
    (NatTrans.congr_app (Picard.Homomorphisms.PoincareDetection.Construction.homogeneousPicardSheafInclusion_toSheafify B) (op B.scheme))
      ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L, hhom⟩
  have hm := ConcreteCategory.congr_hom
    (NatTrans.congr_app (Picard.Homomorphisms.PoincareDetection.Construction.homogeneousPicardSheafInclusion_toSheafify B) (op B.scheme))
      ⟨AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M, B.trivialClass_homogeneous B.scheme⟩
  have hrel : (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B.scheme).app (op B.scheme) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf L) =
      (AbelianModuli.HilbertConstruction.Picard.PicardSheaf.toRelativePicard B.scheme).app (op B.scheme) (AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.classOf M) :=
    hl.symm.trans ((congrArg (B.homogeneousPicardSheafInclusion.hom.app (op B.scheme)) hc).trans hm)
  obtain ⟨e⟩ := NeighborCounting.Field.NormalizedPicardInjection.iso_of_picard_eq B L M hL.some hM.some hrel
  let diagonal : B.scheme ⟶ B.scheme ⊗ B.scheme := lift (𝟙 B.scheme) (𝟙 B.scheme)
  have hz : diagonal ≫ (a ▷ B.scheme) =
      lift (1 : B.scheme ⟶ (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f).scheme) (𝟙 B.scheme) := by
    apply hom_ext <;> simp [diagonal, a]
  exact ⟨(Scheme.Modules.pullbackCongr (congrArg Over.Hom.left hz.symm)).app (quotientDualPoincare D f r).sheaf ≪≫
    (Scheme.Modules.pullbackComp diagonal.left (a ▷ B.scheme).left).symm.app (quotientDualPoincare D f r).sheaf ≪≫
    (Scheme.Modules.pullback diagonal.left).mapIso e ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso diagonal.left⟩

end

/-! Construct full native dual-abelian data for an isogenous quotient,
including its normalized universal Poincare line. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualSheaf.Representation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Field.CharacterKernelQuotient

variable {k : Type} [Field k] {d : ℕ}
variable {A B : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme d (Spec (.of k))}
variable (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A) (f : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny B A) (r : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme.Isogeny A B)

def quotientDualData : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData B where
  abelian := (NeighborCounting.Field.CharacterKernelQuotient.fieldCharacterAbelian D f)
  representable := DualSheaf.Representation.quotientDualRepresentable D f r
  origin := DualSheaf.Representation.quotientDualRepresentable_origin D f r
  poincare := quotientDualPoincare D f r
  poincareHomogeneous := quotientDualPoincare_homogeneous D f r
  universalClass := quotientDualPoincare_universalClass D f r
  normalizedAtAbelianZero := quotientDualPoincare_normalized D f r
  normalizedAtDualZero := quotientDualPoincare_normalizedAtDualZero D f r

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.FieldQuotient.DualAt
