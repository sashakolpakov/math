import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.LocalValuation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.DedekindExtension
import OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.ZeroCover
import OAI.AlgebraicGeometry.Divisors.LineBundles.ValuationModelOrd
import OAI.AlgebraicGeometry.Divisors.LineBundles.PushforwardCompareCongr
import OAI.AlgebraicGeometry.Divisors.LineBundles.ParameterScalarsTower
import OAI.AlgebraicGeometry.Divisors.LineBundles.ParameterResidue
import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularFunction

/-! # Curve Zeros -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CurveZeros.BundleCycles.RelativeCurveZeros

noncomputable section

/-! The positive principal divisor in a proper relative curve pushes
to the generic point of the base with the parameter-extension degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

open OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace OAI.AlgebraicGeometry.Divisors.LineBundles.CurveParameterImage.BundleCycles.CurveParameter OAI.AlgebraicGeometry.Divisors.LineBundles.ParameterBranchesIs.BundleCycles.ParameterBranches OAI.AlgebraicGeometry.Divisors.LineBundles.ParameterScalarsTower.BundleCycles.ParameterScalars
  Normal.LocalValuation.BundleCycles Affine.FractionField.BundleCycles.AffineFractionField PositiveCycleEq.BundleCycles.PositiveCycle IntersectionTheory.ProjectionFormula.CyclePushforward
  IntersectionTheory.ProjectionFormula.Normalization.Scheme GenericFiberEss.BundleCycles.GenericFiberFields

theorem positiveDivisor_pushforward
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [X.IsSeparated] [Y.IsSeparated]
    [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Y) [IsProper f] (hη : f (genericPoint X) = genericPoint Y)
    (gY : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType gY] [LocallyOfFiniteType (f ≫ gY)]
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ gY))
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (g : X.functionField) :
    letI := GenericFiberEss.BundleCycles.GenericFiberFields.fieldAlgebra f hη
    ∀ hg : Transcendental Y.functionField g,
    letI := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra Y.functionField X.functionField g
    letI := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra Y.functionField X.functionField g hg
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (PositiveCycleEq.BundleCycles.PositiveCycle.positivePart (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g)) =
      Finsupp.single (genericPoint Y)
        (Module.finrank (FractionRing (Polynomial Y.functionField)) X.functionField : ℚ) := by
  let := GenericFiberEss.BundleCycles.GenericFiberFields.fieldAlgebra f hη
  intro hg
  let := CurveParameterImage.BundleCycles.CurveParameter.polynomialAlgebra Y.functionField X.functionField g
  let := CurveParameterImage.BundleCycles.CurveParameter.fractionAlgebra Y.functionField X.functionField g hg
  let := ParameterBranchesIs.BundleCycles.ParameterBranches.localAlgebra Y.functionField X.functionField g hg
  let := ParameterBranchesIs.BundleCycles.ParameterBranches.localTower Y.functionField X.functionField g hg
  let := GenericFiberEss.BundleCycles.GenericFiberFields.field_essFiniteType f hη gY
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra gY
  let : CharZero Y.functionField := charZero_of_injective_algebraMap
    ((algebraMap ℂ Y.functionField).injective)
  have htrdeg := GenericFiberEss.BundleCycles.GenericFiberFields.field_trdeg_one f hη gY hdim
  let := CurveParameterImage.BundleCycles.CurveParameter.finite_parameter_extension Y.functionField X.functionField htrdeg g hg
  let := ParameterBranchesIs.BundleCycles.ParameterBranches.closure_dedekind Y.functionField X.functionField g hg htrdeg
  let D : Type := integralClosure (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField) X.functionField
  let : IsFractionRing D X.functionField :=
    integralClosure.isFractionRing_of_finite_extension
      (FractionRing (Polynomial Y.functionField)) X.functionField
  let := ParameterScalarsTower.BundleCycles.ParameterScalars.closureScalarAlgebra Y.functionField X.functionField g hg
  let := ParameterScalarsTower.BundleCycles.ParameterScalars.closureScalarTower Y.functionField X.functionField g hg
  let : IsScalarTower Y.functionField (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField) D := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨i, hi, hf⟩ := DedekindExtension.BundleCycles.RelativeDedekindExtension.exists_extension f hη D
    (IsScalarTower.algebraMap_eq Y.functionField D X.functionField).symm
  have hbase (a : Spec (.of D)) : f (i a) = genericPoint Y := by
    have h := congrArg (fun t : Spec (.of D) ⟶ Y => t a) hf
    exact h.trans (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap_apply Y _)
  have hval (a : Spec (.of D)) : ValuationRing (X.presheaf.stalk (i a)) := by
    let := hNormal (i a)
    exact Normal.LocalValuation.BundleCycles.relativeCurve_stalkValuation f gY hdim (i a) (hbase a)
  let c := RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor (Spec (.of D)) ((Affine.FractionField.BundleCycles.AffineFractionField.fieldIso D X.functionField).inv g)
  have hc : IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward f (PositiveCycleEq.BundleCycles.PositiveCycle.positivePart (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X g)) =
      IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (i ≫ f) c := by
    apply PushforwardCompareCongr.BundleCycles.PushforwardCompare.positivePart_model i f
      (ValuationModelOrd.BundleCycles.ValuationModel.injective D i hi hval) (ValuationModelOrd.BundleCycles.ValuationModel.residueDegree D i hi hval)
    · intro a
      exact congrArg (fun n : ℤ => (n : ℚ)) (ValuationModelOrd.BundleCycles.ValuationModel.ord D i hi hval g a)
    · intro a
      obtain ⟨d, hd⟩ := ParameterScalarsTower.BundleCycles.ParameterScalars.parameter_integer Y.functionField X.functionField g hg
      have hn := RegularFunction.BundleCycles.RegularFunctionOrder.affine_nonneg D X.functionField d a
      rw [hd] at hn
      change (0 : ℚ) ≤ ((Spec (.of D)).ord ((Affine.FractionField.BundleCycles.AffineFractionField.fieldIso D X.functionField).inv g) a : ℚ)
      exact_mod_cast hn
    · intro x hxdeg hx
      have hxpos : 0 < X.ord g x := by
        change (0 : ℚ) < (X.ord g x : ℚ) at hx
        exact_mod_cast hx
      have hxone : coheight x = 1 := by
        by_contra h
        rw [Scheme.ord_eq_zero_of_coheight_neq_one h] at hxpos
        exact (lt_irrefl 0) hxpos
      exact ZeroCover.BundleCycles.RelativeZeroCover.positive_mem_range f hη g hg i hi x
        (CurvePointDimension.BundleCycles.relativeCurve_divisor_image_generic f gY hdim x hxone hxdeg) (hNormal x) hxpos
  let j : Spec (.of D) ⟶ Spec (.of (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField) D))
  let r : Spec (.of (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField)) ⟶ Spec Y.functionField :=
    Spec.map (CommRingCat.ofHom (algebraMap Y.functionField (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField)))
  let b₀ : Y.functionField ⟶ CommRingCat.of (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField) :=
    CommRingCat.ofHom (algebraMap Y.functionField (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField))
  let c₀ : CommRingCat.of (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField) ⟶ CommRingCat.of D :=
    CommRingCat.ofHom (algebraMap (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField) D)
  let a₀ : Y.functionField ⟶ CommRingCat.of D := CommRingCat.ofHom (algebraMap Y.functionField D)
  have habc : a₀ = b₀ ≫ c₀ :=
    congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq Y.functionField (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField) D)
  have hspec : Spec.map a₀ = j ≫ r := (congrArg Spec.map habc).trans (Spec.map_comp b₀ c₀)
  have hcomp : i ≫ f = j ≫ (r ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y) :=
    hf.trans ((congrArg (fun t : Spec (.of D) ⟶ Spec Y.functionField => t ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y) hspec).trans
      (Category.assoc j r (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y)))
  have hnorm : IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward j c = Finsupp.single
      (IsLocalRing.closedPoint (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField) : Spec (.of (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField)))
        (Module.finrank (FractionRing (Polynomial Y.functionField)) X.functionField : ℚ) :=
    ParameterBranchesIs.BundleCycles.ParameterBranches.parameter_divisor_pushforward Y.functionField X.functionField g hg htrdeg
  rw [hc, hcomp]
  have ht := DFunLike.congr_fun (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_comp j (r ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y)) c
  change IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (j ≫ (r ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y)) c =
    IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (r ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y) (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward j c) at ht
  refine ht.trans ((congrArg (IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (r ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y)) hnorm).trans ?_)
  let a : Spec (.of (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField)) := IsLocalRing.closedPoint (LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField)
  let b : Spec Y.functionField := IsLocalRing.closedPoint Y.functionField
  let n : ℕ := Module.finrank (FractionRing (Polynomial Y.functionField)) X.functionField
  have hs := IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward_single (r ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y) a (n : ℚ)
  have hr : r a = b := Subsingleton.elim (α := PrimeSpectrum Y.functionField) _ _
  have hp : (r ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y) a = genericPoint Y := IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap_apply Y _
  have hdR : r.residueDegree a = 1 := ParameterResidue.BundleCycles.ParameterResidueDegree.zero_place_residueDegree Y.functionField
  have hdY : (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y).residueDegree b = 1 :=
    BirationalStalk.BundleCycles.BirationalStalkResidueDegree.fromSpecStalk_residueDegree Y (genericPoint Y)
  have hdY' : (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y).residueDegree (r a) = 1 :=
    (congrArg (fun z : Spec Y.functionField => (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y).residueDegree z) hr).trans hdY
  have hd : (r ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y).residueDegree a = 1 :=
    (IntersectionTheory.ProjectionFormula.CyclePushforward.residueDegree_comp r (IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y) a).trans (by rw [hdR, hdY', mul_one])
  change IntersectionTheory.ProjectionFormula.CyclePushforward.pointPushforward (r ≫ IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap Y) (Finsupp.single a (n : ℚ)) =
    Finsupp.single (genericPoint Y) (n : ℚ)
  exact hs.trans (by rw [hp, hd, Nat.cast_one, mul_one])

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.CurveZeros.BundleCycles.RelativeCurveZeros
