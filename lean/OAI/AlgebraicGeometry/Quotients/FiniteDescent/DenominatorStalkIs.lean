import OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorSheafEq
import OAI.AlgebraicGeometry.Quotients.FiniteDescent.SmoothStalk

/-! # Denominator Stalk Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorStalkIs.Construction.DenominatorStalk

noncomputable section

/-! The denominator ideal at a stalk, and its principality on smooth integral schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} [IsIntegral X]

theorem map_stalk (r : X.functionField) (U : X.affineOpens) (x : U.1) :
    ((DenominatorSheafEq.Construction.DenominatorSheaf.data r).ideal U).map (X.presheaf.germ U.1 x x.2).hom =
      DenominatorIdealEq.Construction.DenominatorIdeal.ideal (R := X.presheaf.stalk x) r := by
  have : Nonempty U.1 := ⟨x⟩
  change (DenominatorSheafEq.Construction.DenominatorSheaf.affineIdeal r U).map _ = _
  rw [DenominatorSheafEq.Construction.DenominatorSheaf.affineIdeal_eq]
  let := X.presheaf.algebra_section_stalk x
  have := U.2.isLocalization_stalk x
  have := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  have : Module.Flat Γ(X, U) (X.presheaf.stalk x) :=
    IsLocalization.flat _ (U.2.primeIdealOf x).asIdeal.primeCompl
  exact DenominatorBase.Construction.DenominatorBaseChange.map (R := Γ(X, U)) (S := X.presheaf.stalk x)
    (F := X.functionField) r

theorem isPrincipal {K : Type u} [Field K] [IsAlgClosed K]
    (f : X ⟶ Spec (.of K)) [Smooth f] (r : X.functionField) (x : X) :
    (DenominatorIdealEq.Construction.DenominatorIdeal.ideal (R := X.presheaf.stalk x) r).IsPrincipal := by
  have := SmoothStalk.Construction.SmoothStalkFactorial.stalk f x
  exact DenominatorIdealEq.Construction.DenominatorIdeal.isPrincipal r

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.DenominatorStalkIs.Construction.DenominatorStalk
