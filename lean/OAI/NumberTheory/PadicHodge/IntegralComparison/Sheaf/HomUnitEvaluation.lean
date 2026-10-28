import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomUnit

/-! # Hom Unit Evaluation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.HomUnitEvaluation

noncomputable section

/-! Evaluation at an actual structure-sheaf map is a native
module-sheaf morphism, with literal sectionwise normalization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {X : Scheme.{u}} (M N : X.Modules)
  (v : ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X ⟶ M)

def map : ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N ⟶ N :=
  ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomFunctoriality.Construction.sheafHomMap v (𝟙 N) ≫ ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomUnit.Construction.sheafHomUnitMap N

theorem app (U : X.Opens) (q : Γ(ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule M N, U)) :
    (map M N v).app U q =
      ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomEvaluation.Construction.sheafHomEvalAtOpen M N U q (v.app U (1 : Γ(X, U))) := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.HomUnitEvaluation
