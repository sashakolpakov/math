import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEquationSupport
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Open.BaseFunctorRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Smooth.ReducedFibers

/-! # Smooth Equation Open Support -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEquationOpenSupport

noncomputable section

/-! Equality on an open part of a reduced noetherian parameter scheme
pulls back to arbitrary test schemes. No reducedness assumption on the
test or on its total source is needed. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem equation_of_open_support {S : Scheme.{0}} {X Y : Over S}
    [Smooth X.hom] [IsSeparated Y.hom] (l r : X ⟶ Y)
    (U : S.Opens) [IsReduced U.toScheme] [IsLocallyNoetherian U.toScheme]
    (hU : (U : Set S) ⊆ SmoothEquationSupport.smoothEquationSupport l r)
    {T : Scheme.{0}} (t : T ⟶ S) (ht : ∀ x : T, t x ∈ U) :
    (Over.pullback t).map l = (Over.pullback t).map r := by
  have : IsReduced (pullback X.hom U.ι) := AbelianModuli.HilbertConstruction.Smooth.ReducedFibers.smooth_reducedSource (pullback.snd X.hom U.ι)
  have h := SmoothEquationSupport.equation_of_support_range l r U.ι (by
    rw [Scheme.Opens.range_ι]
    exact hU)
  have he := PullbackEquationProjection.pullback_equation_precomp l r U.ι (Open.BaseFunctorRepresentation.OpenBaseTest.lift U (Over.mk t) ht) h
  have hfac : Open.BaseFunctorRepresentation.OpenBaseTest.lift U (Over.mk t) ht ≫ U.ι = t :=
    Open.BaseFunctorRepresentation.OpenBaseTest.lift_ι U (Over.mk t) ht
  rw [hfac] at he
  exact he

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEquationOpenSupport
