import OAI.NumberTheory.PadicHodge.GeometricComparison.CoefficientQuotientNatural
import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryDeRhamIs

/-! # Ordinary De Rham Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryDeRhamLevel.OrdinaryDeRhamReductionLevel

noncomputable section

/-! Ordinary de Rham coefficient reduction commutes with an actual target
algebra map and a corresponding coefficient-ideal transition. -/

open _root_.CategoryTheory

universe u
variable (R : Type u) [CommRing R] (I J : Ideal R) (hIJ : I ≤ J)
  {A B C : CommAlgCat.{u} R} (α : A ⟶ B) (β : A ⟶ C) (g : B ⟶ C)
  (hB : ∀ r, r ∈ I → algebraMap R B r = 0)
  (hC : ∀ r, r ∈ J → algebraMap R C r = 0) (h : α ≫ g = β)

include h in
theorem natural : OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction.map R I α hB ≫ IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map g =
    IntegralComparison.Module.IdealQuotientTransition.complexMap R I J hIJ (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.complex R A) ≫
      OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction.map R J β hC :=
  CoefficientQuotientNatural.CoefficientQuotientLiftTransition.natural R I J hIJ
    (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map α) (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map β) (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map g)
    (OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction.kernel R I α hB)
    (OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction.kernel R J β hC)
    ((IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map_comp α g).symm.trans (congrArg IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.map h))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryDeRhamLevel.OrdinaryDeRhamReductionLevel
