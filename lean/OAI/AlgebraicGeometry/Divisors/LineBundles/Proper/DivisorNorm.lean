import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.BirationalPrincipalDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.NormalizationFactors
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.NormalizationDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationDivisorPushforward

/-! # Divisor Norm -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.DivisorNorm.BundleCycles.ProperDivisorNorm

noncomputable section

/-! Principal divisors commute with proper generically finite pushforward.
The normal-target case factors through finite relative normalization and
the proved proper birational comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalFactorTo.BundleCycles.BirationalFactor OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalFactorTo.BundleCycles.BirationalFactorFields
  Relative.Normalization.BundleCycles.RelativeNormalization Relative.NormalizationFields.BundleCycles.RelativeNormalizationFields IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
  (f : X ⟶ Y) [IsProper f] (hη : f (genericPoint X) = genericPoint Y)
  (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY]
  (hfinite : letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
    Module.Finite Y.functionField X.functionField)

include gY hfinite in
/-- Proper generically finite pushforward over a base whose divisor
stalks are DVRs is the principal divisor of the native field norm. -/
theorem principalDivisor_norm_of_dvr
    (hDVR : ∀ y : Y, coheight y = 1 → IsDiscreteValuationRing (Y.presheaf.stalk y))
    (g : X.functionField) (hg : g ≠ 0) :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) =
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y (Algebra.norm Y.functionField g) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  let := hfinite
  let : AlgebraicGeometry.IsNoetherian (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) :=
    NormalizationResidue.BundleCycles.finiteNormalization_noetherian X (f ≫ gY)
  let : AlgebraicGeometry.IsNoetherian (BirationalFactorTo.BundleCycles.BirationalFactor.intermediate f hη) :=
    Relative.NormalizationDivisor.BundleCycles.RelativeNormalizationDivisor.relativeNormalization_noetherian Y X.functionField gY
  let : IsFinite (BirationalFactorTo.BundleCycles.BirationalFactor.intermediateMap f hη) := Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap_isFinite Y X.functionField gY
  let : IsProper (BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor f hη) := NormalizationFactors.BundleCycles.BirationalFactor.birationalFactor_isProper f hη (f ≫ gY)
  let := BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor_fieldMap_isIso f hη hfinite
  let : Algebra Y.functionField (BirationalFactorTo.BundleCycles.BirationalFactor.intermediate f hη).functionField :=
    (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactorTo.BundleCycles.BirationalFactor.intermediateMap f hη) (BirationalFactorTo.BundleCycles.BirationalFactorFields.intermediateMap_genericPoint f hη)).hom.toAlgebra
  let e := BirationalFactorTo.BundleCycles.BirationalFactorFields.factorFunctionFieldIso f hη hfinite
  have hge : e.hom g ≠ 0 := (map_ne_zero_iff e.hom.hom e.commRingCatIsoToRingEquiv.injective).mpr hg
  have hDVRZ : ∀ z : BirationalFactorTo.BundleCycles.BirationalFactor.intermediate f hη, coheight z = 1 →
      IsDiscreteValuationRing ((BirationalFactorTo.BundleCycles.BirationalFactor.intermediate f hη).presheaf.stalk z) :=
    fun z hz => Relative.NormalizationLocal.BundleCycles.RelativeNormalizationLocal.stalk_isDVR Y X.functionField gY z hz
  have hb := BirationalPrincipalDivisor.BundleCycles.properBirational_principalDivisor_pushforward
    (BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor f hη) (BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor_genericPoint f hη)
    (BirationalFactorTo.BundleCycles.BirationalFactor.intermediateMap f hη ≫ gY) hDVRZ (e.hom g)
  rw [BirationalFactorTo.BundleCycles.BirationalFactorFields.factorFunctionFieldIso_pullback] at hb
  have hn := Relative.NormalizationDivisor.BundleCycles.RelativeNormalizationDivisor.principalDivisor_native_norm Y X.functionField gY
    hDVR (e.hom g) hge
  have hs := NormalizationDivisorPushforward.BundleCycles.normalizationPrincipalDivisor_pushforward X (f ≫ gY) g hg
  calc
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) =
        IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X)
          (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) ((IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g))) :=
      congrArg (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f) hs.symm
    _ = IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (BirationalFactorTo.BundleCycles.BirationalFactor.intermediateMap f hη) (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor f hη)
          (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) ((IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g))) := by
      rw [← LinearMap.comp_apply, ← IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp, ← BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor_comp,
        IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp, LinearMap.comp_apply]
    _ = RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y (Algebra.norm Y.functionField (e.hom g)) := by
      rw [hb]
      exact hn
    _ = RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y (Algebra.norm Y.functionField g) := by
      rw [BirationalFactorTo.BundleCycles.BirationalFactorFields.factorFunctionFieldIso_norm]

include gY hfinite in
/-- For every proper generically finite morphism of integral finite-type
schemes in characteristic zero, a principal divisor pushes to the
principal divisor of its actual function-field norm. The schemes may be
singular: their finite normalizations supply the comparison. -/
theorem principalDivisor_norm (g : X.functionField) (hg : g ≠ 0) :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) =
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y (Algebra.norm Y.functionField g) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  let := hfinite
  let : AlgebraicGeometry.IsNoetherian (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) :=
    NormalizationResidue.BundleCycles.finiteNormalization_noetherian X (f ≫ gY)
  let : AlgebraicGeometry.IsNoetherian (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization Y) :=
    NormalizationResidue.BundleCycles.finiteNormalization_noetherian Y gY
  let : IsFinite (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y) := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap_isFinite Y gY
  let F := NormalizationFunctorTo.BundleCycles.NormalizationFunctor.normalizationLift f hη
  have hF : F (genericPoint (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X)) = genericPoint (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization Y) :=
    NormalizationFunctorTo.BundleCycles.NormalizationFunctor.normalizationLift_genericPoint f hη
  let : IsProper F := NormalizationFactors.BundleCycles.NormalizationFunctor.normalizationLift_isProper f hη (f ≫ gY)
  let : Algebra (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization Y).functionField (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X).functionField :=
    (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap F hF).hom.toAlgebra
  have hfinrank : Module.finrank Y.functionField X.functionField =
      Module.finrank (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization Y).functionField (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X).functionField :=
    Algebra.finrank_eq_of_equiv_equiv (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso Y).commRingCatIsoToRingEquiv
      (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).commRingCatIsoToRingEquiv
      (congrArg CommRingCat.Hom.hom (NormalizationFunctorTo.BundleCycles.NormalizationFunctor.normalizationFieldMap_square f hη))
  have hfiniteF : Module.Finite (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization Y).functionField (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X).functionField :=
    Module.finite_of_finrank_pos (hfinrank ▸ Module.finrank_pos)
  have hgX : (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g ≠ 0 :=
    (map_ne_zero_iff (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom.hom (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldMap_bijective X).injective).mpr hg
  have hn := principalDivisor_norm_of_dvr F hF (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y ≫ gY) hfiniteF
    (fun y hy => IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization_stalk_isDVR Y gY y hy) ((IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g) hgX
  rw [← NormalizationFunctorTo.BundleCycles.NormalizationFunctor.normalizationLift_norm f hη] at hn
  have hsX := NormalizationDivisorPushforward.BundleCycles.normalizationPrincipalDivisor_pushforward X (f ≫ gY) g hg
  have hsY := NormalizationDivisorPushforward.BundleCycles.normalizationPrincipalDivisor_pushforward Y gY
    (Algebra.norm Y.functionField g) (Algebra.norm_ne_zero_iff.mpr hg)
  calc
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) =
        IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap X)
          (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) ((IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g))) :=
      congrArg (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f) hsX.symm
    _ = IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y) (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward F
          (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) ((IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g))) := by
      rw [← LinearMap.comp_apply, ← IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp,
        ← NormalizationFunctorTo.BundleCycles.NormalizationFunctor.normalizationLift_comp f hη,
        IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp, LinearMap.comp_apply]
    _ = RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y (Algebra.norm Y.functionField g) := by
      rw [hn]
      exact hsY

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.DivisorNorm.BundleCycles.ProperDivisorNorm
