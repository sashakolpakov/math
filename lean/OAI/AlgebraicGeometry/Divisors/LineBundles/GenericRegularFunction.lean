import OAI.AlgebraicGeometry.Divisors.LineBundles.GenericFieldComposition
import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor

/-! # Generic Regular Function -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GenericRegularFunction.BundleCycles

noncomputable section

/-! # LineBundleCycles: generic-stalk pullback of an actual global regular function -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u

theorem genericFieldMap_globalFunction {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y) (a : Γ(Y, ⊤)) :
    Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη (RegularDivisor.BundleCycles.globalFunctionFieldElement Y a) =
      RegularDivisor.BundleCycles.globalFunctionFieldElement X (f.appTop a) :=
  ConcreteCategory.congr_hom (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap_germ f hη) a

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GenericRegularFunction.BundleCycles
