import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationStalkMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.MorphismOrderStalk

/-! # Normalization Local Divisor -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationLocalDivisor.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the global normalized divisor restricts to the actual normalized stalk

The local normalization is finite over the original Noetherian stalk.
The actual normalized-stalk map preserves the generic field, local
rings, and codimensions. Every coefficient of the global principal
divisor therefore restricts to the local principal divisor, including
coefficients at poles.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

variable (X : Scheme) [IsIntegral X]
variable (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] (x : U)

def normalizationLocalFieldMap :
    (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X).functionField ⟶
      (Spec (CommRingCat.of (integralClosure (X.presheaf.stalk x) X.functionField))).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (NormalizationStalkMap.BundleCycles.normalizationStalkMap X U hU x) (NormalizationStalkMap.BundleCycles.normalizationStalkMap_genericPoint X U hU x)

instance normalizationLocalFieldMap_isIso : IsIso (normalizationLocalFieldMap X U hU x) := by
  let := NormalizationStalkMap.BundleCycles.normalizationStalkMap_stalkMap_isIso X U hU x
    (genericPoint (Spec (CommRingCat.of (integralClosure (X.presheaf.stalk x) X.functionField))))
  unfold normalizationLocalFieldMap Cycles.Functoriality.FunctionFields.Construction.genericFieldMap
  infer_instance

variable [AlgebraicGeometry.IsNoetherian X]
variable (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

omit [Nonempty U] in
include f in
theorem normalizationLocalRing_noetherian : IsNoetherianRing (integralClosure (X.presheaf.stalk x) X.functionField) := by
  let : Module.Finite (X.presheaf.stalk x) (integralClosure (X.presheaf.stalk x) X.functionField) :=
    IntersectionTheory.ProjectionFormula.Support.Normalization.finite_stalk_normalization f x
  exact IsNoetherianRing.of_finite (X.presheaf.stalk x) _

include f in
theorem normalizationLocal_ord (g : (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X).functionField)
    (y : Spec (CommRingCat.of (integralClosure (X.presheaf.stalk x) X.functionField))) :
    letI := NormalizationResidue.BundleCycles.finiteNormalization_noetherian X f
    letI := normalizationLocalRing_noetherian X U x f
    (Spec (CommRingCat.of (integralClosure (X.presheaf.stalk x) X.functionField))).ord
        (normalizationLocalFieldMap X U hU x g) y =
      (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X).ord g (NormalizationStalkMap.BundleCycles.normalizationStalkMap X U hU x y) := by
  let := NormalizationResidue.BundleCycles.finiteNormalization_noetherian X f
  let := normalizationLocalRing_noetherian X U x f
  let := NormalizationStalkMap.BundleCycles.normalizationStalkMap_stalkMap_isIso X U hU x y
  let : IsIso (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (NormalizationStalkMap.BundleCycles.normalizationStalkMap X U hU x)
      (NormalizationStalkMap.BundleCycles.normalizationStalkMap_genericPoint X U hU x)) := normalizationLocalFieldMap_isIso X U hU x
  exact MorphismOrderStalk.BundleCycles.ord_of_stalkMap_isIso (NormalizationStalkMap.BundleCycles.normalizationStalkMap X U hU x) (NormalizationStalkMap.BundleCycles.normalizationStalkMap_genericPoint X U hU x)
    y (NormalizationStalkMap.BundleCycles.normalizationStalkMap_coheight X U hU x y) g

theorem normalizationLocal_principalDivisor (g : (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X).functionField) :
    letI := NormalizationResidue.BundleCycles.finiteNormalization_noetherian X f
    letI := normalizationLocalRing_noetherian X U x f
    Finsupp.comapDomain (NormalizationStalkMap.BundleCycles.normalizationStalkMap X U hU x) (Ord.BundleCycles.principalDivisor (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) g)
      (NormalizationStalkMap.BundleCycles.normalizationStalkMap_injective X U hU x).injOn =
      Ord.BundleCycles.principalDivisor (Spec (CommRingCat.of (integralClosure (X.presheaf.stalk x) X.functionField)))
        (normalizationLocalFieldMap X U hU x g) := by
  let := NormalizationResidue.BundleCycles.finiteNormalization_noetherian X f
  let := normalizationLocalRing_noetherian X U x f
  ext y
  exact (normalizationLocal_ord X U hU x f g y).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationLocalDivisor.BundleCycles
