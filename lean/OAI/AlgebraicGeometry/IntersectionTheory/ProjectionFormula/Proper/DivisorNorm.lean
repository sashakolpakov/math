import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalPrincipalDivisor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalFactorFields
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.NormalizationDivisor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.DivisorComparison

/-! # Divisor Norm -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.DivisorNorm

noncomputable section

/-! Principal divisors commute with proper generically finite pushforward.
The normal-target case factors through finite relative normalization and
the proved proper birational comparison. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Fields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalFactor OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.BirationalFactorFields
  Relative.Normalization Relative.NormalizationFields Affine.DivisorNorm CyclePushforward

variable {k : Type} [Field k] [CharZero k]
  {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
  (f : X ⟶ Y) [IsProper f] (hη : f (genericPoint X) = genericPoint Y)
  (gY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType gY]
  (hfinite : letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
    Module.Finite Y.functionField X.functionField)

include gY hfinite in
/-- Proper generically finite pushforward over a base whose divisor
stalks are DVRs is the principal divisor of the native field norm. -/
theorem principalDivisor_norm_of_dvr
    (hDVR : ∀ y : Y, coheight y = 1 → IsDiscreteValuationRing (Y.presheaf.stalk y))
    (g : X.functionField) (hg : g ≠ 0) :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
    CyclePushforward.pointPushforward f (Affine.DivisorNorm.rationalPrincipalDivisor X g) =
      Affine.DivisorNorm.rationalPrincipalDivisor Y (Algebra.norm Y.functionField g) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  let := hfinite
  let : AlgebraicGeometry.IsNoetherian (Normalization.Scheme.normalization X) :=
    Normalization.DivisorComparison.normalization_noetherian X (f ≫ gY)
  let : AlgebraicGeometry.IsNoetherian (BirationalFactor.intermediate f hη) :=
    Relative.NormalizationDivisor.relativeNormalization_noetherian Y X.functionField gY
  let : IsFinite (BirationalFactor.intermediateMap f hη) := Relative.Normalization.relativeNormalizationMap_isFinite Y X.functionField gY
  let : IsProper (BirationalFactor.birationalFactor f hη) := BirationalFactor.birationalFactor_isProper f hη (f ≫ gY)
  let := BirationalFactor.birationalFactor_fieldMap_isIso f hη hfinite
  let : Algebra Y.functionField (BirationalFactor.intermediate f hη).functionField :=
    (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (BirationalFactor.intermediateMap f hη) (BirationalFactorFields.intermediateMap_genericPoint f hη)).hom.toAlgebra
  let e := BirationalFactorFields.factorFunctionFieldIso f hη hfinite
  have hge : e.hom g ≠ 0 := (map_ne_zero_iff e.hom.hom e.commRingCatIsoToRingEquiv.injective).mpr hg
  have hDVRZ : ∀ z : BirationalFactor.intermediate f hη, coheight z = 1 →
      IsDiscreteValuationRing ((BirationalFactor.intermediate f hη).presheaf.stalk z) :=
    fun z hz => Relative.NormalizationLocal.stalk_isDVR Y X.functionField gY z hz
  have hb := BirationalPrincipalDivisor.principalDivisor_pushforward
    (BirationalFactor.birationalFactor f hη) (BirationalFactor.birationalFactor_genericPoint f hη)
    (BirationalFactor.intermediateMap f hη ≫ gY) hDVRZ (e.hom g)
  rw [BirationalFactorFields.factorFunctionFieldIso_pullback] at hb
  have hn := Relative.NormalizationDivisor.principalDivisor_native_norm Y X.functionField gY
    hDVR (e.hom g) hge
  have hs := Normalization.DivisorComparison.normalization_principalDivisor X (f ≫ gY) g hg
  calc
    CyclePushforward.pointPushforward f (Affine.DivisorNorm.rationalPrincipalDivisor X g) =
        CyclePushforward.pointPushforward f (CyclePushforward.pointPushforward (Normalization.Scheme.normalizationMap X)
          (Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.Scheme.normalization X) ((Normalization.Fields.normalizationFieldIso X).hom g))) :=
      congrArg (CyclePushforward.pointPushforward f) hs.symm
    _ = CyclePushforward.pointPushforward (BirationalFactor.intermediateMap f hη) (CyclePushforward.pointPushforward (BirationalFactor.birationalFactor f hη)
          (Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.Scheme.normalization X) ((Normalization.Fields.normalizationFieldIso X).hom g))) := by
      rw [← LinearMap.comp_apply, ← CyclePushforward.pointPushforward_comp, ← BirationalFactor.birationalFactor_comp,
        CyclePushforward.pointPushforward_comp, LinearMap.comp_apply]
    _ = Affine.DivisorNorm.rationalPrincipalDivisor Y (Algebra.norm Y.functionField (e.hom g)) := by
      rw [hb]
      exact hn
    _ = Affine.DivisorNorm.rationalPrincipalDivisor Y (Algebra.norm Y.functionField g) := by
      rw [BirationalFactorFields.factorFunctionFieldIso_norm]

include gY hfinite in
/-- For every proper generically finite morphism of integral finite-type
schemes in characteristic zero, a principal divisor pushes to the
principal divisor of its actual function-field norm. The schemes may be
singular: their finite normalizations supply the comparison. -/
theorem principalDivisor_norm (g : X.functionField) (hg : g ≠ 0) :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
    CyclePushforward.pointPushforward f (Affine.DivisorNorm.rationalPrincipalDivisor X g) =
      Affine.DivisorNorm.rationalPrincipalDivisor Y (Algebra.norm Y.functionField g) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  let := hfinite
  let : AlgebraicGeometry.IsNoetherian (Normalization.Scheme.normalization X) :=
    Normalization.DivisorComparison.normalization_noetherian X (f ≫ gY)
  let : AlgebraicGeometry.IsNoetherian (Normalization.Scheme.normalization Y) :=
    Normalization.DivisorComparison.normalization_noetherian Y gY
  let : IsFinite (Normalization.Scheme.normalizationMap Y) := Normalization.Scheme.normalizationMap_isFinite Y gY
  let F := Normalization.Functor.normalizationLift f hη
  have hF : F (genericPoint (Normalization.Scheme.normalization X)) = genericPoint (Normalization.Scheme.normalization Y) :=
    Normalization.Functor.normalizationLift_genericPoint f hη
  let : IsProper F := Normalization.Functor.normalizationLift_isProper f hη (f ≫ gY)
  let : Algebra (Normalization.Scheme.normalization Y).functionField (Normalization.Scheme.normalization X).functionField :=
    (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap F hF).hom.toAlgebra
  have hfinrank : Module.finrank Y.functionField X.functionField =
      Module.finrank (Normalization.Scheme.normalization Y).functionField (Normalization.Scheme.normalization X).functionField :=
    Algebra.finrank_eq_of_equiv_equiv (Normalization.Fields.normalizationFieldIso Y).commRingCatIsoToRingEquiv
      (Normalization.Fields.normalizationFieldIso X).commRingCatIsoToRingEquiv
      (congrArg CommRingCat.Hom.hom (Normalization.Functor.normalizationFieldMap_square f hη))
  have hfiniteF : Module.Finite (Normalization.Scheme.normalization Y).functionField (Normalization.Scheme.normalization X).functionField :=
    Module.finite_of_finrank_pos (hfinrank ▸ Module.finrank_pos)
  have hgX : (Normalization.Fields.normalizationFieldIso X).hom g ≠ 0 :=
    (map_ne_zero_iff (Normalization.Fields.normalizationFieldIso X).hom.hom (Normalization.Fields.normalizationFieldMap_bijective X).injective).mpr hg
  have hn := principalDivisor_norm_of_dvr F hF (Normalization.Scheme.normalizationMap Y ≫ gY) hfiniteF
    (fun y hy => Normalization.Scheme.normalization_stalk_isDVR Y gY y hy) ((Normalization.Fields.normalizationFieldIso X).hom g) hgX
  rw [← Normalization.Functor.normalizationLift_norm f hη] at hn
  have hsX := Normalization.DivisorComparison.normalization_principalDivisor X (f ≫ gY) g hg
  have hsY := Normalization.DivisorComparison.normalization_principalDivisor Y gY
    (Algebra.norm Y.functionField g) (Algebra.norm_ne_zero_iff.mpr hg)
  calc
    CyclePushforward.pointPushforward f (Affine.DivisorNorm.rationalPrincipalDivisor X g) =
        CyclePushforward.pointPushforward f (CyclePushforward.pointPushforward (Normalization.Scheme.normalizationMap X)
          (Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.Scheme.normalization X) ((Normalization.Fields.normalizationFieldIso X).hom g))) :=
      congrArg (CyclePushforward.pointPushforward f) hsX.symm
    _ = CyclePushforward.pointPushforward (Normalization.Scheme.normalizationMap Y) (CyclePushforward.pointPushforward F
          (Affine.DivisorNorm.rationalPrincipalDivisor (Normalization.Scheme.normalization X) ((Normalization.Fields.normalizationFieldIso X).hom g))) := by
      rw [← LinearMap.comp_apply, ← CyclePushforward.pointPushforward_comp,
        ← Normalization.Functor.normalizationLift_comp f hη,
        CyclePushforward.pointPushforward_comp, LinearMap.comp_apply]
    _ = Affine.DivisorNorm.rationalPrincipalDivisor Y (Algebra.norm Y.functionField g) := by
      rw [hn]
      exact hsY

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Proper.DivisorNorm
