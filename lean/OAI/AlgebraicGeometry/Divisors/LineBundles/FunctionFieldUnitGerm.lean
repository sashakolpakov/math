import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalBoundary

/-! # Function Field Unit Germ -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.FunctionFieldUnitGerm.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual unit-valued function-field germs and their restriction laws -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X : Scheme.{0}} [IsIntegral X]

def functionFieldUnitGerm (U : X.Opens) [Nonempty U] : Γ(X, U)ˣ →* X.functionFieldˣ :=
  Units.map (X.germToFunctionField U).hom.toMonoidHom

theorem functionFieldUnitGerm_restrict {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) (a : Γ(X, U)ˣ) :
    functionFieldUnitGerm V (Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom a) =
      functionFieldUnitGerm U a := by
  apply Units.ext
  exact RationalBoundary.BundleCycles.RationalUnitRepresentative.germ_restrict h a.val

theorem functionFieldUnitGerm_order [IsLocallyNoetherian X] (U : X.Opens) [Nonempty U]
    (a : Γ(X, U)ˣ) (x : X) (hx : x ∈ U) : X.ord (functionFieldUnitGerm U a).val x = 0 :=
  Scheme.ord_of_isUnit a.isUnit hx

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.FunctionFieldUnitGerm.BundleCycles
