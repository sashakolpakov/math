import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.FiberDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.DedekindExtension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ZeroCover
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ValuationModel
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardCompare
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Scalars
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ResidueDegree
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.FunctionOrder

/-! # Curve Zeros -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.CurveZeros

noncomputable section

/-! The positive principal divisor in a proper relative curve pushes
to the generic point of the base with the parameter-extension degree. -/

set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Place OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveParameter OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Branches OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Scalars
  Affine.DivisorNorm Affine.FractionField PositiveCycle CyclePushforward
  Normalization.Scheme Generic.FiberFields

theorem positiveDivisor_pushforward {K : Type} [Field K] [CharZero K]
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [X.IsSeparated] [Y.IsSeparated]
    [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Y) [IsProper f] (hη : f (genericPoint X) = genericPoint Y)
    (gY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType gY] [LocallyOfFiniteType (f ≫ gY)]
    (hdim : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension gY + 1 = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ gY))
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (g : X.functionField) :
    letI := Generic.FiberFields.fieldAlgebra f hη
    ∀ hg : Transcendental Y.functionField g,
    letI := CurveParameter.polynomialAlgebra Y.functionField X.functionField g
    letI := CurveParameter.fractionAlgebra Y.functionField X.functionField g hg
    CyclePushforward.pointPushforward f (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor X g)) =
      Finsupp.single (genericPoint Y)
        (Module.finrank (FractionRing (Polynomial Y.functionField)) X.functionField : ℚ) := by
  let := Generic.FiberFields.fieldAlgebra f hη
  intro hg
  let := CurveParameter.polynomialAlgebra Y.functionField X.functionField g
  let := CurveParameter.fractionAlgebra Y.functionField X.functionField g hg
  let := Parameter.Branches.localAlgebra Y.functionField X.functionField g hg
  let := Parameter.Branches.localTower Y.functionField X.functionField g hg
  let := Generic.FiberFields.field_essFiniteType f hη gY
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra gY
  let : CharZero Y.functionField := charZero_of_injective_algebraMap
    ((algebraMap K Y.functionField).injective)
  have htrdeg := Generic.FiberFields.field_trdeg_one f hη gY hdim
  let := CurveParameter.finite_parameter_extension Y.functionField X.functionField htrdeg g hg
  let := Parameter.Branches.closure_dedekind Y.functionField X.functionField g hg htrdeg
  let D : Type := integralClosure (ProjectionFormula.Polynomial.Place.localRing Y.functionField) X.functionField
  let : IsFractionRing D X.functionField :=
    integralClosure.isFractionRing_of_finite_extension
      (FractionRing (Polynomial Y.functionField)) X.functionField
  let := Parameter.Scalars.closureScalarAlgebra Y.functionField X.functionField g hg
  let := Parameter.Scalars.closureScalarTower Y.functionField X.functionField g hg
  let : IsScalarTower Y.functionField (ProjectionFormula.Polynomial.Place.localRing Y.functionField) D := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨i, hi, hf⟩ := DedekindExtension.exists_extension f hη D
    (IsScalarTower.algebraMap_eq Y.functionField D X.functionField).symm
  have hbase (a : Spec (.of D)) : f (i a) = genericPoint Y := by
    have h := congrArg (fun t : Spec (.of D) ⟶ Y => t a) hf
    exact h.trans (Normalization.Scheme.genericMap_apply Y _)
  have hval (a : Spec (.of D)) : ValuationRing (X.presheaf.stalk (i a)) := by
    let := hNormal (i a)
    exact Generic.FiberDimension.stalk_valuation f gY hdim (i a) (hbase a)
  let c := Affine.DivisorNorm.rationalPrincipalDivisor (Spec (.of D)) ((Affine.FractionField.fieldIso D X.functionField).inv g)
  have hc : CyclePushforward.pointPushforward f (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor X g)) =
      CyclePushforward.pointPushforward (i ≫ f) c := by
    apply PushforwardCompare.positivePart_model i f
      (ValuationModel.injective D i hi hval) (ValuationModel.residueDegree D i hi hval)
    · intro a
      exact congrArg (fun n : ℤ => (n : ℚ)) (ValuationModel.ord D i hi hval g a)
    · intro a
      obtain ⟨d, hd⟩ := Parameter.Scalars.parameter_integer Y.functionField X.functionField g hg
      have hn := Regular.FunctionOrder.affine_nonneg D X.functionField d a
      rw [hd] at hn
      change (0 : ℚ) ≤ ((Spec (.of D)).ord ((Affine.FractionField.fieldIso D X.functionField).inv g) a : ℚ)
      exact_mod_cast hn
    · intro x hxdeg hx
      have hxpos : 0 < X.ord g x := by
        change (0 : ℚ) < (X.ord g x : ℚ) at hx
        exact_mod_cast hx
      have hxone : coheight x = 1 := by
        by_contra h
        rw [Scheme.ord_eq_zero_of_coheight_neq_one h] at hxpos
        exact (lt_irrefl 0) hxpos
      exact ZeroCover.positive_mem_range f hη g hg i hi x
        (Generic.FiberDimension.image_eq_genericPoint f gY hdim x hxone hxdeg) (hNormal x) hxpos
  let j : Spec (.of D) ⟶ Spec (.of (ProjectionFormula.Polynomial.Place.localRing Y.functionField)) :=
    Spec.map (CommRingCat.ofHom (algebraMap (ProjectionFormula.Polynomial.Place.localRing Y.functionField) D))
  let r : Spec (.of (ProjectionFormula.Polynomial.Place.localRing Y.functionField)) ⟶ Spec Y.functionField :=
    Spec.map (CommRingCat.ofHom (algebraMap Y.functionField (ProjectionFormula.Polynomial.Place.localRing Y.functionField)))
  have hcomp : i ≫ f = j ≫ (r ≫ Normalization.Scheme.genericMap Y) := by
    set_option backward.isDefEq.respectTransparency false in
      rw [hf, ← Category.assoc]
      congr 1
      dsimp only [j, r]
      rw [← Spec.map_comp]
      congr 1
  have hnorm : CyclePushforward.pointPushforward j c = Finsupp.single
      (IsLocalRing.closedPoint (ProjectionFormula.Polynomial.Place.localRing Y.functionField) : Spec (.of (ProjectionFormula.Polynomial.Place.localRing Y.functionField)))
        (Module.finrank (FractionRing (Polynomial Y.functionField)) X.functionField : ℚ) :=
    Parameter.Branches.parameter_divisor_pushforward Y.functionField X.functionField g hg htrdeg
  rw [hc, hcomp]
  have ht := DFunLike.congr_fun (CyclePushforward.pointPushforward_comp j (r ≫ Normalization.Scheme.genericMap Y)) c
  change CyclePushforward.pointPushforward (j ≫ (r ≫ Normalization.Scheme.genericMap Y)) c =
    CyclePushforward.pointPushforward (r ≫ Normalization.Scheme.genericMap Y) (CyclePushforward.pointPushforward j c) at ht
  refine ht.trans ((congrArg (CyclePushforward.pointPushforward (r ≫ Normalization.Scheme.genericMap Y)) hnorm).trans ?_)
  have hs := CyclePushforward.pointPushforward_single (r ≫ Normalization.Scheme.genericMap Y)
    (IsLocalRing.closedPoint (ProjectionFormula.Polynomial.Place.localRing Y.functionField) : Spec (.of (ProjectionFormula.Polynomial.Place.localRing Y.functionField)))
    (Module.finrank (FractionRing (Polynomial Y.functionField)) X.functionField : ℚ)
  have hr : r (IsLocalRing.closedPoint (ProjectionFormula.Polynomial.Place.localRing Y.functionField)) =
      (IsLocalRing.closedPoint Y.functionField : Spec Y.functionField) :=
    Subsingleton.elim (α := PrimeSpectrum Y.functionField) _ _
  have hp : (r ≫ Normalization.Scheme.genericMap Y) (IsLocalRing.closedPoint (ProjectionFormula.Polynomial.Place.localRing Y.functionField)) =
      genericPoint Y := Normalization.Scheme.genericMap_apply Y _
  have hd : (r ≫ Normalization.Scheme.genericMap Y).residueDegree (IsLocalRing.closedPoint (ProjectionFormula.Polynomial.Place.localRing Y.functionField)) = 1 := by
    have hdR : r.residueDegree (IsLocalRing.closedPoint (ProjectionFormula.Polynomial.Place.localRing Y.functionField)) = 1 :=
      Parameter.ResidueDegree.zero_place_residueDegree Y.functionField
    have hdY : (Normalization.Scheme.genericMap Y).residueDegree (IsLocalRing.closedPoint Y.functionField) = 1 :=
      Stalk.ResidueDegree.fromSpecStalk_residueDegree Y (genericPoint Y)
    set_option backward.isDefEq.respectTransparency false in
      rw [CyclePushforward.residueDegree_comp, hr, hdR, hdY, mul_one]
  set_option backward.isDefEq.respectTransparency false in
    simpa only [hp, hd, Nat.cast_one, mul_one] using hs

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.CurveZeros
