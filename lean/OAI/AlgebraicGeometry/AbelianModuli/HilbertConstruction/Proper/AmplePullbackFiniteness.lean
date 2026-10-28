import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.RationalFiberFiniteMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.FiniteClosedFibers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.FiberClosedSupport

/-! # Ample Pullback Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AmplePullbackFiniteness

noncomputable section

/-! A proper morphism to a scheme locally of finite type over an algebraically closed field is finite if the pullback of one line bundle is ample. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem proper_isFinite_of_ample_pullback
    {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (p : Y ⟶ Spec (.of K)) [LocallyOfFiniteType p] [IsSeparated p]
    (L : Line.Bundles.LineBundle Y) (hL : (L.pullback f).IsAmple) : IsFinite f := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  apply FiniteClosedFibers.proper_isFinite_of_finite_closedFibers f
  apply Rational.FiberClosedSupport.closedFiber_finite_of_rationalFibers f p
  intro a ha
  have : IsClosedImmersion (a ≫ p) := ha.symm ▸ inferInstanceAs (IsClosedImmersion (𝟙 (Spec (.of K))))
  have : IsClosedImmersion a := IsClosedImmersion.of_comp a p
  exact Ample.RationalFiberFiniteMorphism.ample_pullback_rationalFiber_isFinite f a L hL

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Proper.AmplePullbackFiniteness
