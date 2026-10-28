import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ZeroCover
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.FiberFields

/-! # Zero Cover -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ZeroCover

noncomputable section

/-! Zeros above the generic point of an integral base are covered by
the corresponding normalized parameter model. The ground field acts
through the actual morphism's generic and point-stalk maps. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Place OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Branches OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.FiberFields OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Scheme

theorem positive_mem_range {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [X.IsSeparated]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y) (g : X.functionField) :
    letI := Generic.FiberFields.fieldAlgebra f hη
    ∀ hg : Transcendental Y.functionField g,
    letI := Parameter.Branches.localAlgebra Y.functionField X.functionField g hg
    ∀ (i : Spec (.of (integralClosure (Polynomial.Place.localRing Y.functionField) X.functionField)) ⟶ X),
      Spec.map (CommRingCat.ofHom (algebraMap (integralClosure (Polynomial.Place.localRing Y.functionField) X.functionField)
        X.functionField)) ≫ i = Normalization.Scheme.genericMap X →
      ∀ x : X, f x = genericPoint Y → IsIntegrallyClosed (X.presheaf.stalk x) →
        0 < X.ord g x → x ∈ Set.range i := by
  let := Generic.FiberFields.fieldAlgebra f hη
  intro hg
  let := Parameter.Branches.localAlgebra Y.functionField X.functionField g hg
  intro i hi x hx hn hp
  let := hn
  let B := X.presheaf.stalk x
  let D := integralClosure (Polynomial.Place.localRing Y.functionField) X.functionField
  let := Generic.FiberFields.stalkAlgebra f x hx
  let := Generic.FiberFields.stalkTower f hη x hx
  have hg0 : g ≠ 0 := fun h => hg (h ▸ isAlgebraic_zero)
  obtain ⟨b, hb, hbg⟩ := PositiveOrder.exists_stalk_element x g hg0 hp
  let j₀ := Parameter.LocalMap.localMap Y.functionField B b hb
  let : Algebra (Polynomial.Place.localRing Y.functionField) B := j₀.toAlgebra
  let : IsScalarTower (Polynomial.Place.localRing Y.functionField) B X.functionField :=
    IsScalarTower.of_algebraMap_eq'
      (Parameter.LocalMap.localMap_field Y.functionField B b hb X.functionField g hg hbg).symm
  let j := Local.IntegralModelLift.lift (Polynomial.Place.localRing Y.functionField) D B X.functionField
  apply ModelImage.mem_range_of_stalk_lift D i hi x j
  ext a
  exact Local.IntegralModelLift.algebraMap_lift (Polynomial.Place.localRing Y.functionField) D B X.functionField a

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Relative.ZeroCover
