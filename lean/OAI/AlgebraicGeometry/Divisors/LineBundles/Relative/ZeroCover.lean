import OAI.AlgebraicGeometry.Divisors.LineBundles.ParameterBranchesIs
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ModelLift
import OAI.AlgebraicGeometry.Divisors.LineBundles.PositiveOrderIs
import OAI.AlgebraicGeometry.Divisors.LineBundles.ModelImageOf
import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiberEss

/-! # Zero Cover -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.ZeroCover.BundleCycles.RelativeZeroCover

noncomputable section

/-! Zeros above the generic point of an integral base are covered by
the corresponding normalized parameter model. The ground field acts
through the actual morphism's generic and point-stalk maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.Place.BundleCycles.PolynomialPlace OAI.AlgebraicGeometry.Divisors.LineBundles.ParameterBranchesIs.BundleCycles.ParameterBranches OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFiberEss.BundleCycles.GenericFiberFields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

theorem positive_mem_range {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [X.IsSeparated]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y) (g : X.functionField) :
    letI := GenericFiberEss.BundleCycles.GenericFiberFields.fieldAlgebra f hη
    ∀ hg : Transcendental Y.functionField g,
    letI := ParameterBranchesIs.BundleCycles.ParameterBranches.localAlgebra Y.functionField X.functionField g hg
    ∀ (i : Spec (.of (integralClosure (Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField) X.functionField)) ⟶ X),
      Spec.map (CommRingCat.ofHom (algebraMap (integralClosure (Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField) X.functionField)
        X.functionField)) ≫ i = IntersectionTheory.ProjectionFormula.Normalization.Scheme.genericMap X →
      ∀ x : X, f x = genericPoint Y → IsIntegrallyClosed (X.presheaf.stalk x) →
        0 < X.ord g x → x ∈ Set.range i := by
  let := GenericFiberEss.BundleCycles.GenericFiberFields.fieldAlgebra f hη
  intro hg
  let := ParameterBranchesIs.BundleCycles.ParameterBranches.localAlgebra Y.functionField X.functionField g hg
  intro i hi x hx hn hp
  let := hn
  let B := X.presheaf.stalk x
  let D := integralClosure (Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField) X.functionField
  let := GenericFiberEss.BundleCycles.GenericFiberFields.stalkAlgebra f x hx
  let := GenericFiberEss.BundleCycles.GenericFiberFields.stalkTower f hη x hx
  have hg0 : g ≠ 0 := fun h => hg (h ▸ isAlgebraic_zero)
  obtain ⟨b, hb, hbg⟩ := PositiveOrderIs.BundleCycles.PositiveOrder.exists_stalk_element x g hg0 hp
  let j₀ := ParameterBranchesIs.BundleCycles.ParameterLocalMap.localMap Y.functionField B b hb
  let : Algebra (Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField) B := j₀.toAlgebra
  let : IsScalarTower (Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField) B X.functionField :=
    IsScalarTower.of_algebraMap_eq'
      (ParameterBranchesIs.BundleCycles.ParameterLocalMap.localMap_field Y.functionField B b hb X.functionField g hg hbg).symm
  let j := Integral.ModelLift.BundleCycles.IntegralModelLift.lift (Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField) D B X.functionField
  apply ModelImageOf.BundleCycles.ModelImage.mem_range_of_stalk_lift D i hi x j
  ext a
  exact Integral.ModelLift.BundleCycles.IntegralModelLift.algebraMap_lift (Polynomial.Place.BundleCycles.PolynomialPlace.localRing Y.functionField) D B X.functionField a

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Relative.ZeroCover.BundleCycles.RelativeZeroCover
