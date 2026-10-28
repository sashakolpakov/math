import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.GeometricClassDescent
import OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.MapCharacterization

/-! # Cycle Class -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.CycleClass.BundleCycles

noncomputable section

/-! The independently defined geometric cycle class descends to
LineBundleCycles's actual rational Chow quotient in every codimension. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

def geometricCycleClassQ (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    Chow.BundleCycles.ChowQ X p ⟶ X.rationalCohomology (p + p) :=
  ModuleCat.ofHom ((Chow.BundleCycles.rationalEquivalenceQ X p).liftQ (X.geometricCycleClassMap p)
    (Principal.GeometricClassDescent.BundleCycles.rationalEquivalenceQ_geometricClass_ker X p))

theorem geometricCycleClassQ_cycle (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (z : X.RationalDimensionCycle p) :
    geometricCycleClassQ X p (Chow.BundleCycles.cycleToChowQ X p z) = X.geometricCycleClassMap p z := rfl

theorem geometricCycleClassQ_isGeometric (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) :
    MapCharacterization.BundleCycles.IsGeometricCycleClass X p (geometricCycleClassQ X p) := geometricCycleClassQ_cycle X p

theorem geometricCycleClassQ_eq_of_isGeometric (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (cl : Chow.BundleCycles.ChowQ X p ⟶ X.rationalCohomology (p + p)) (hcl : MapCharacterization.BundleCycles.IsGeometricCycleClass X p cl) :
    cl = geometricCycleClassQ X p :=
  MapCharacterization.BundleCycles.isGeometricCycleClass_unique X p cl (geometricCycleClassQ X p) hcl (geometricCycleClassQ_isGeometric X p)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Geometric.CycleClass.BundleCycles
