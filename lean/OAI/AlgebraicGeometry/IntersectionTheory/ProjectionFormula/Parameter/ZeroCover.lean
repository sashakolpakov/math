import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.LocalMap
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.IntegralModelLift
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ModelImage
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FunctionDivisor

/-! # Zero Cover -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ZeroCover

noncomputable section

/-! Every zero on a normal scheme is covered by the normalized zero
parameter model, whenever that model has its prescribed birational map.
The proof constructs the actual coordinate-ring map into the zero's stalk. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.Place OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.Branches OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FunctionDivisor
  Normalization.Scheme

theorem positive_mem_range {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] [X.IsSeparated] (f : X ⟶ Spec (.of k)) (g : X.functionField) :
    letI := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
    ∀ hg : Transcendental k g,
    letI := Branches.localAlgebra k X.functionField g hg
    ∀ (i : Spec (.of (integralClosure (Polynomial.Place.localRing k) X.functionField)) ⟶ X),
      Spec.map (CommRingCat.ofHom (algebraMap (integralClosure (Polynomial.Place.localRing k) X.functionField)
        X.functionField)) ≫ i = Normalization.Scheme.genericMap X →
      ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) → 0 < X.ord g x → x ∈ Set.range i := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  intro hg
  let := Branches.localAlgebra k X.functionField g hg
  intro i hi x hn hp
  let := hn
  let B := X.presheaf.stalk x
  let D := integralClosure (Polynomial.Place.localRing k) X.functionField
  let := FunctionDivisor.stalkScalarAlgebra f x
  let := FunctionDivisor.stalkScalarTower f x
  have hg0 : g ≠ 0 := fun h => hg (h ▸ isAlgebraic_zero)
  obtain ⟨b, hb, hbg⟩ := PositiveOrder.exists_stalk_element x g hg0 hp
  let j₀ := LocalMap.localMap k B b hb
  let : Algebra (Polynomial.Place.localRing k) B := j₀.toAlgebra
  let : IsScalarTower (Polynomial.Place.localRing k) B X.functionField :=
    IsScalarTower.of_algebraMap_eq'
      (LocalMap.localMap_field k B b hb X.functionField g hg hbg).symm
  let j := Local.IntegralModelLift.lift (Polynomial.Place.localRing k) D B X.functionField
  apply ModelImage.mem_range_of_stalk_lift D i hi x j
  ext a
  exact Local.IntegralModelLift.algebraMap_lift (Polynomial.Place.localRing k) D B X.functionField a

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ZeroCover
