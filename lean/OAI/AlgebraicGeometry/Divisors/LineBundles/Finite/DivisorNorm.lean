import OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalFactorTo
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.RelativeIsomorphism
import OAI.AlgebraicGeometry.Divisors.LineBundles.IsomorphismDivisorPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.NormalizationDivisorPushforward
import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.FunctionFields
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.DivisorLaws

/-! # Divisor Norm -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Divisors.LineBundles.Finite.DivisorNorm.BundleCycles.FiniteDivisorNorm

/-! Principal divisors commute with finite dominant pushforward.
The normal-target case factors through finite relative normalization and
the proved finite birational isomorphism comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalFactorTo.BundleCycles.BirationalFactor OAI.AlgebraicGeometry.Divisors.LineBundles.BirationalFactorTo.BundleCycles.BirationalFactorFields
  Relative.Normalization.BundleCycles.RelativeNormalization Relative.NormalizationFields.BundleCycles.RelativeNormalizationFields IntersectionTheory.ProjectionFormula.CyclePushforward

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
  (f : X ⟶ Y) [IsFinite f] (hη : f (genericPoint X) = genericPoint Y)
  (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY]

include gY in
/-- Finite dominant pushforward over a base whose divisor
stalks are DVRs is the principal divisor of the native field norm. -/
theorem principalDivisor_norm_of_dvr
    (hDVR : ∀ y : Y, coheight y = 1 → IsDiscreteValuationRing (Y.presheaf.stalk y))
    (g : X.functionField) (hg : g ≠ 0) :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) =
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y (Algebra.norm Y.functionField g) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  have hfinite := FunctionFields.BundleCycles.finiteMorphism_functionField_finite f hη
  let := hfinite
  let : AlgebraicGeometry.IsNoetherian (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) :=
    NormalizationResidue.BundleCycles.finiteNormalization_noetherian X (f ≫ gY)
  let : AlgebraicGeometry.IsNoetherian (BirationalFactorTo.BundleCycles.BirationalFactor.intermediate f hη) :=
    Relative.NormalizationDivisor.BundleCycles.RelativeNormalizationDivisor.relativeNormalization_noetherian Y X.functionField gY
  let : IsFinite (BirationalFactorTo.BundleCycles.BirationalFactor.intermediateMap f hη) := Relative.Normalization.BundleCycles.RelativeNormalization.relativeNormalizationMap_isFinite Y X.functionField gY
  let : IsFinite (BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor f hη) := BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor_isFinite f hη (f ≫ gY)
  let := BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor_fieldMap_isIso f hη hfinite
  let : Algebra Y.functionField (BirationalFactorTo.BundleCycles.BirationalFactor.intermediate f hη).functionField :=
    (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactorTo.BundleCycles.BirationalFactor.intermediateMap f hη) (BirationalFactorTo.BundleCycles.BirationalFactorFields.intermediateMap_genericPoint f hη)).hom.toAlgebra
  let e := BirationalFactorTo.BundleCycles.BirationalFactorFields.factorFunctionFieldIso f hη hfinite
  have hge : e.hom g ≠ 0 := (map_ne_zero_iff e.hom.hom e.commRingCatIsoToRingEquiv.injective).mpr hg
  let : IsIso (BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor f hη) :=
    @RelativeIsomorphism.BundleCycles.finiteBirational_relativeNormalization_isIso Y inferInstance X.functionField inferInstance
      inferInstance hfinite (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) inferInstance (BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor f hη)
      (BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor_isFinite f hη (f ≫ gY)) (BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor_genericPoint f hη)
      (BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor_fieldMap_isIso f hη hfinite)
  have hb := IsomorphismDivisorPushforward.BundleCycles.isomorphismPrincipalDivisor_pushforward
    (BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor f hη) (BirationalFactorTo.BundleCycles.BirationalFactor.birationalFactor_genericPoint f hη) (e.hom g)
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

include gY in
/-- For every finite dominant morphism of integral finite-type
schemes in characteristic zero, a principal divisor pushes to the
principal divisor of its actual function-field norm. The schemes may be
singular: their finite normalizations supply the comparison. -/
theorem principalDivisor_norm (g : X.functionField) (hg : g ≠ 0) :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g) =
      RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y (Algebra.norm Y.functionField g) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  have hfinite := FunctionFields.BundleCycles.finiteMorphism_functionField_finite f hη
  let := hfinite
  let : AlgebraicGeometry.IsNoetherian (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X) :=
    NormalizationResidue.BundleCycles.finiteNormalization_noetherian X (f ≫ gY)
  let : AlgebraicGeometry.IsNoetherian (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization Y) :=
    NormalizationResidue.BundleCycles.finiteNormalization_noetherian Y gY
  let : IsFinite (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y) := IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap_isFinite Y gY
  let F := NormalizationFunctorTo.BundleCycles.NormalizationFunctor.normalizationLift f hη
  have hF : F (genericPoint (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X)) = genericPoint (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization Y) :=
    NormalizationFunctorTo.BundleCycles.NormalizationFunctor.normalizationLift_genericPoint f hη
  let : IsFinite F := NormalizationFunctorTo.BundleCycles.NormalizationFunctor.normalizationLift_isFinite f hη (f ≫ gY)
  let : Algebra (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization Y).functionField (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalization X).functionField :=
    (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap F hF).hom.toAlgebra
  have hgX : (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom g ≠ 0 :=
    (map_ne_zero_iff (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldIso X).hom.hom (IntersectionTheory.ProjectionFormula.Normalization.Fields.normalizationFieldMap_bijective X).injective).mpr hg
  have hn := principalDivisor_norm_of_dvr F hF (IntersectionTheory.ProjectionFormula.Normalization.Scheme.normalizationMap Y ≫ gY)
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

end AlgebraicGeometry.Divisors.LineBundles.Finite.DivisorNorm.BundleCycles.FiniteDivisorNorm

namespace AlgebraicGeometry.Divisors.LineBundles.Finite.DivisorNorm.BundleCycles

/-! # LineBundleCycles: finite pushforward of a genuinely pulled rational principal divisor gives the generic residue degree -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem rationalPrincipalPointDivisor_pow (X : Scheme.{0}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (g : X.functionField) (hg : g ≠ 0) (n : ℕ) :
    RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (g ^ n) = (n : ℚ) • RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g := by
  induction n with
  | zero =>
    change (Ord.BundleCycles.principalDivisor X (g ^ 0)).mapRange _ _ = _
    rw [pow_zero, Principal.DivisorLaws.BundleCycles.principalDivisor_one, Finsupp.mapRange_zero, Nat.cast_zero, zero_smul]
  | succ n ih =>
    have hm : RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (g ^ n * g) =
        RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (g ^ n) + RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g := by
      change (Ord.BundleCycles.principalDivisor X (g ^ n * g)).mapRange _ _ = _
      rw [Ord.BundleCycles.principalDivisor_mul X _ _ (pow_ne_zero n hg) hg, Finsupp.mapRange_add Int.cast_add]
      rfl
    rw [pow_succ, hm, ih, Nat.cast_add, Nat.cast_one, add_smul, one_smul]

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (hη : f (genericPoint X) = genericPoint Y)
    (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY]

include gY in
theorem finitePushforward_pulledPrincipalDivisor (g : Y.functionFieldˣ) :
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g.val)) =
      (f.residueDegree (genericPoint X) : ℚ) • RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y g.val := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  have hg : Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g.val ≠ 0 :=
    (map_ne_zero_iff (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom
      (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.injective).mpr g.ne_zero
  have hn := FiniteDivisorNorm.principalDivisor_norm f hη gY (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g.val) hg
  have hp : Algebra.norm Y.functionField (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη g.val) =
      g.val ^ f.residueDegree (genericPoint X) := by
    change Algebra.norm Y.functionField (algebraMap Y.functionField X.functionField g.val) = _
    rw [Algebra.norm_algebraMap, IntersectionTheory.ProjectionFormula.Support.Fields.genericFieldMap_finrank_eq_residueDegree f hη]
  exact hn.trans ((congrArg (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor Y) hp).trans
    (rationalPrincipalPointDivisor_pow Y g.val g.ne_zero _))

end AlgebraicGeometry.Divisors.LineBundles.Finite.DivisorNorm.BundleCycles

end

end OAI
