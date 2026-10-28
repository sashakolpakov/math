import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFieldComposition
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.Normalization

/-! # Function Fields -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.FunctionFields.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite dominant morphisms induce finite actual function-field extensions
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem finiteMorphism_functionField_finite (f : X ⟶ Y) [IsFinite f]
    (hη : f (genericPoint X) = genericPoint Y) :
    letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
    Module.Finite Y.functionField X.functionField := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  let y := genericPoint Y
  let U : Y.Opens := (Y.affineCover.f (Y.affineCover.idx y)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (Y.affineCover.f _)
  let : Nonempty U := ⟨⟨y, Y.affineCover.covers y⟩⟩
  let : Nonempty (f ⁻¹ᵁ U) := ⟨⟨genericPoint X, by
    change f (genericPoint X) ∈ U
    rw [hη]
    exact Y.affineCover.covers y⟩⟩
  let A := Γ(Y, U)
  let B := Γ(X, f ⁻¹ᵁ U)
  let : Algebra A B := (f.app U).hom.toAlgebra
  let : Module.Finite A B := f.finite_app U hU
  let := functionField_isFractionRing_of_isAffineOpen Y U hU
  let := functionField_isFractionRing_of_isAffineOpen X (f ⁻¹ᵁ U) (hU.preimage f)
  let : Algebra A X.functionField :=
    ((Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.comp (Y.germToFunctionField U).hom).toAlgebra
  let : IsScalarTower A Y.functionField X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A B X.functionField := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (Deformation.FunctionField.BundleCycles.genericFieldMap_germOn f hη U))
  have hi : Function.Injective (algebraMap A X.functionField) :=
    (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.injective.comp (Y.germToFunctionField_injective U)
  exact IntersectionTheory.ProjectionFormula.Finite.Normalization.finite_fraction_extension A B Y.functionField X.functionField hi

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.FunctionFields.BundleCycles
