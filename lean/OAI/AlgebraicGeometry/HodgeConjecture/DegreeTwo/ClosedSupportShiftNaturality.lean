import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.GoodShiftFunctorNaturality
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.SupportSectionChanges

/-! # Closed Support Shift Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportShiftNaturality.Constructions

noncomputable section

/-! Specified-support changes commute with the cohomology comparison for the actual Thom degree shift. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{0}} (O U P W : Opens X)
variable (α : ClosedSupportIs.Constructions.closedSupportSectionFunctor (R := ℚ) O U ⟶ ClosedSupportIs.Constructions.closedSupportSectionFunctor P W)
variable (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℚ) X) ℕ)
variable (hK : ∀ n, TopCat.Sheaf.IsFlasque (K.X n))
variable (k : ℕ) (he : ∀ n, n<k → K.ExactAt n)

theorem closedSupportGoodShiftCohomologyIso_naturality (n : ℕ) :
    HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app
        (K.truncGE' (RelativeCupHomotopy.Constructions.cochainDegreeShiftEmbedding k))) n ≫
        (ClosedSupportExactnessShift.Constructions.closedSupportGoodShiftCohomologyIso P W K hK k he n).hom =
      (ClosedSupportExactnessShift.Constructions.closedSupportGoodShiftCohomologyIso O U K hK k he n).hom ≫
        HomologicalComplex.homologyMap ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app K) (k+n) :=
  GoodShiftFunctorNaturality.Constructions.goodShiftFunctorCohomologyIso_functor_naturality
    (ClosedSupportIs.Constructions.closedSupportSectionFunctor O U) (ClosedSupportIs.Constructions.closedSupportSectionFunctor P W) α K k _ _ n

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ClosedSupportShiftNaturality.Constructions
