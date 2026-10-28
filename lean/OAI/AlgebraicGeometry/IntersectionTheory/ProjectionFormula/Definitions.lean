import OAI.AlgebraicTopology.Products.CapCompatibility
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

/-! # Definitions -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Definitions

noncomputable section

/-! Definitions used in the ProjectionFormula statement. -/

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Products.CapCompatibility

section

abbrev HQ (X : TopCat.{0}) (k : ℕ) :=
  AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) X k

abbrev BQ (X : TopCat.{0}) (k : ℕ) :=
  (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) X).homology k

/-- Proposed interface for an oriented rational Poincaré space.
The sign converts the library's front-cap convention to the convention
adjoint to integration of `test ∪ class`. -/
structure PoincareData (X : TopCat.{0}) (d : ℕ) where
  fundamental : BQ X d
  duality : ∀ p q : ℕ, p + q = d → HQ X p ≃ₗ[ℚ] BQ X q
  duality_apply :
    ∀ (p q : ℕ) (h : p + q = d) (a : HQ X p),
      duality p q h a =
        (-1 : ℚ) ^ (p * q) •
          AlgebraicTopology.Products.CapBoundary.singularCapHomology (R := ℚ) X p q a
            (cast (congrArg (fun k => (BQ X k : Type)) h.symm)
              fundamental)

/-- Pushforward is constructed from duality and actual homology pushforward. -/
def pushforward
    {X Y : TopCat.{0}} {m n : ℕ}
    (DX : PoincareData X m) (DY : PoincareData Y n)
    (f : X ⟶ Y) (a b r : ℕ)
    (hX : a + r = m) (hY : b + r = n) :
    HQ X a →ₗ[ℚ] HQ Y b :=
  (DY.duality b r hY).symm.toLinearMap.comp
    ((AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f r).hom.comp
      (DX.duality a r hX).toLinearMap)

end

open _root_.AlgebraicGeometry

/-- Geometric intersection relation, not an assumed bilinear map. -/
abbrev chowIntersection := ProperCycleLinearity.chowIntersection

/-- Relation induced by the constructed proper pushforward on cycles. -/
abbrev chowPushforward {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) (p q : ℕ) := ProperCycleLinearity.chowPushforward f p q

/-- Graph-intersection pullback relation, independent of LineBundleCycles's operation stub. -/
abbrev chowPullback {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (P : ProperCycleLinearity.ProductPresentation X Y) (f : X.toOver ⟶ Y.toOver) (n p : ℕ) :=
  ProperCycleLinearity.chowPullback P f n p

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Definitions
