import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.RegularStratum
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SupportedCycleClass

/-! # Support Over -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportOver.BundleCycles

noncomputable section

/-! Restriction of a nonempty integral support to an open subscheme is
compatible with the actual complex base and preserves its codimension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularSupport.Constructions

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (i : X ⟶ Y) [IsOpenImmersion i.left] (B : IrreducibleCloseds Y.left)
    [Nonempty (SupportRestriction.BundleCycles.openSupportPullback i.left B)]

local notation "A" => OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction.BundleCycles.openRestrictedSupport i.left B

def openRestrictedSupportOverMap : CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver X A ⟶ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportOver Y B :=
  Over.homMk (SupportRestriction.BundleCycles.openRestrictedSupportMap i.left B) (by
    change SupportRestriction.BundleCycles.openRestrictedSupportMap i.left B ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι B ≫ Y.hom) = CycleClass.Geometric.GenericPoint.reducedSupportι A ≫ X.hom
    rw [← Category.assoc, SupportRestriction.BundleCycles.openRestrictedSupportMap_inclusion, Category.assoc, i.w])

instance openRestrictedSupportOverMap_open : IsOpenImmersion (openRestrictedSupportOverMap i B).left :=
  inferInstanceAs (IsOpenImmersion (SupportRestriction.BundleCycles.openRestrictedSupportMap i.left B))

omit [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] in
theorem openRestrictedSupportOverMap_inclusion :
    openRestrictedSupportOverMap i B ≫ CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient Y B = CycleClass.Thom.Scheme.RegularSupport.Constructions.supportToAmbient X A ≫ i :=
  Over.OverMorphism.ext (SupportRestriction.BundleCycles.openRestrictedSupportMap_inclusion i.left B)

omit [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] in
theorem openRestrictedSupportOver_dimension :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension A X.hom = Foundations.Scheme.SupportDimension.supportTranscendenceDimension B Y.hom := by
  have h := SupportRestriction.BundleCycles.openRestrictedSupport_dimension i.left B Y.hom
  rw [i.w] at h
  exact h

include i in
omit [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] in
theorem openImmersionOver_dimension [IsIntegral X.left] [IsIntegral Y.left] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom := by
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion i.left Y.hom
  rw [i.w] at h
  exact h

omit [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] in
theorem openRestrictedSupportOver_codimension [IsIntegral X.left] [IsIntegral Y.left]
    (p : ℕ) (hp : Foundations.Scheme.SupportDimension.supportTranscendenceDimension B Y.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension Y.hom) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension A X.hom + p = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension X.hom := by
  rw [openRestrictedSupportOver_dimension, openImmersionOver_dimension i]
  exact hp

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportOver.BundleCycles
