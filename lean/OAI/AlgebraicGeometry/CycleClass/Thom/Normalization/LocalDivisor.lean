import OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.StalkMap
import OAI.AlgebraicGeometry.CycleClass.Thom.MorphismOrderStalk
import OAI.AlgebraicGeometry.CycleClass.Thom.SupportNormalization

/-! # Local Divisor -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.LocalDivisor.Constructions

noncomputable section

/-!
# ThomClass: the global normalized divisor restricts to the actual normalized stalk

The local normalization is finite over the original Noetherian stalk.
The actual normalized-stalk map preserves the generic field, local
rings, and codimensions. Every coefficient of the global principal
divisor therefore restricts to the local principal divisor, including
coefficients at poles.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Scheme.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.Field.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.MorphismOrderStalk.Constructions

variable (X : Scheme) [IsIntegral X]
variable (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (x : U)

def normalizationLocalFieldMap :
    (Normalization.Scheme.Constructions.normalization X).functionField ⟶
      (Spec (CommRingCat.of (integralClosure (X.presheaf.stalk x) X.functionField))).functionField :=
  RationalOrderTransport.Constructions.genericFieldMap (StalkMap.Constructions.Local.normalizationStalkMap X U hU x) (StalkMap.Constructions.Local.normalizationStalkMap_genericPoint X U hU x)

instance normalizationLocalFieldMap_isIso : IsIso (normalizationLocalFieldMap X U hU x) := by
  let := StalkMap.Constructions.Local.normalizationStalkMap_stalkMap_isIso X U hU x
    (genericPoint (Spec (CommRingCat.of (integralClosure (X.presheaf.stalk x) X.functionField))))
  unfold normalizationLocalFieldMap RationalOrderTransport.Constructions.genericFieldMap
  infer_instance

variable [AlgebraicGeometry.IsNoetherian X]
variable (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

omit [Nonempty U] in
include f in
theorem normalizationLocalRing_noetherian : IsNoetherianRing (integralClosure (X.presheaf.stalk x) X.functionField) := by
  let : Module.Finite (X.presheaf.stalk x) (integralClosure (X.presheaf.stalk x) X.functionField) :=
    SupportNormalization.Constructions.finite_stalk_normalization f x
  exact IsNoetherianRing.of_finite (X.presheaf.stalk x) _

include f in
theorem normalizationLocal_ord (g : (Normalization.Scheme.Constructions.normalization X).functionField)
    (y : Spec (CommRingCat.of (integralClosure (X.presheaf.stalk x) X.functionField))) :
    letI := Field.Constructions.finiteNormalization_noetherian X f
    letI := normalizationLocalRing_noetherian X U x f
    (Spec (CommRingCat.of (integralClosure (X.presheaf.stalk x) X.functionField))).ord
        (normalizationLocalFieldMap X U hU x g) y =
      (Normalization.Scheme.Constructions.normalization X).ord g (StalkMap.Constructions.Local.normalizationStalkMap X U hU x y) := by
  let := Field.Constructions.finiteNormalization_noetherian X f
  let := normalizationLocalRing_noetherian X U x f
  let := StalkMap.Constructions.Local.normalizationStalkMap_stalkMap_isIso X U hU x y
  let : IsIso (RationalOrderTransport.Constructions.genericFieldMap (StalkMap.Constructions.Local.normalizationStalkMap X U hU x)
      (StalkMap.Constructions.Local.normalizationStalkMap_genericPoint X U hU x)) := normalizationLocalFieldMap_isIso X U hU x
  exact MorphismOrderStalk.Constructions.ord_of_stalkMap_isIso (StalkMap.Constructions.Local.normalizationStalkMap X U hU x) (StalkMap.Constructions.Local.normalizationStalkMap_genericPoint X U hU x)
    y (StalkMap.Constructions.Local.normalizationStalkMap_coheight X U hU x y) g

theorem normalizationLocal_principalDivisor (g : (Normalization.Scheme.Constructions.normalization X).functionField) :
    letI := Field.Constructions.finiteNormalization_noetherian X f
    letI := normalizationLocalRing_noetherian X U x f
    Finsupp.comapDomain (StalkMap.Constructions.Local.normalizationStalkMap X U hU x) (Divisors.LineBundles.Ord.BundleCycles.principalDivisor (Normalization.Scheme.Constructions.normalization X) g)
      (StalkMap.Constructions.Local.normalizationStalkMap_injective X U hU x).injOn =
      Divisors.LineBundles.Ord.BundleCycles.principalDivisor (Spec (CommRingCat.of (integralClosure (X.presheaf.stalk x) X.functionField)))
        (normalizationLocalFieldMap X U hU x g) := by
  let := Field.Constructions.finiteNormalization_noetherian X f
  let := normalizationLocalRing_noetherian X U x f
  ext y
  exact (normalizationLocal_ord X U hU x f g y).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.LocalDivisor.Constructions
