import OAI.ArithmeticGeometry.Descent.CMVariety.SplitPeriods
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Finite Geometric Points -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.FiniteGeometricPoints.Abelian

noncomputable section

/-!
Convert finiteness of genuine complex points of a finite-type scheme to
scheme-theoretic isolation. This uses the closed-point correspondence and
the Jacobson property, so generic scheme points are not silently treated
as complex-valued points.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- Complex-valued points that respect the given complex structure map. -/
def ComplexModuliPoints (X : Over (Spec (CommRingCat.of ℂ))) :=
  {p : Spec (CommRingCat.of ℂ) ⟶ X.left // p ≫ X.hom = 𝟙 _}

/-- Finitely many complex-valued points force a locally finite-type
complex scheme to have the discrete Zariski topology. -/
theorem discrete_of_finite_complex_moduli_points
    (X : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType X.hom]
    [Finite (ComplexModuliPoints X)] : DiscreteTopology X.left := by
  have : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have : Finite (closedPoints X.left) :=
    Finite.of_equiv (ComplexModuliPoints X) (pointEquivClosedPoint X.hom)
  exact JacobsonSpace.discreteTopology (Set.toFinite _)

/-- An injective classification by the proved finite set of split CM
periods yields actual scheme-theoretic isolation. The classification map
and its injectivity must be constructed from the geometry separately. -/
theorem isolated_of_injective_split_period_map
    {U : Type*} [AddCommGroup U] [Module ℚ U]
    {H : OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} (D : OAI.AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition H)
    (X : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType X.hom]
    (period : ComplexModuliPoints X → SplitPeriods.Abelian.SplitCMPeriod D)
    (hperiod : Function.Injective period) (p : ComplexModuliPoints X) :
    IsOpen {p.val (IsLocalRing.closedPoint ℂ)} := by
  have : Finite (SplitPeriods.Abelian.SplitCMPeriod D) := SplitPeriods.Abelian.split_CM_periods_finite D
  have : Finite (ComplexModuliPoints X) := Finite.of_injective period hperiod
  have : DiscreteTopology X.left := discrete_of_finite_complex_moduli_points X
  exact isOpen_discrete _

end

end OAI.ArithmeticGeometry.Descent.CMVariety.FiniteGeometricPoints.Abelian
