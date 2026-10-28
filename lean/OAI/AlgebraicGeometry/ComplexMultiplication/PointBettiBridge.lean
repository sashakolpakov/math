import OAI.AlgebraicGeometry.ComplexMultiplication.PointTopologyEquality
import OAI.AlgebraicGeometry.ComplexMultiplication.SingularCochainBridge
import OAI.AlgebraicGeometry.Betti.Scheme

/-! # Point Betti Bridge -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.PointBettiBridge

noncomputable section

/-! # Betti cohomology of the unchanged scheme-point space

The comparison is the identity on actual scheme points, followed by evaluation
of genuine singular cochains. Both directions intertwine actual scheme maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

/-- The identity homeomorphism on the same actual complex scheme points. -/
def complexPointSpaceIso (X : _root_.CategoryTheory.Over (Spec (.of ℂ))) :
    Betti.Scheme.schemePointSpace X ≅ TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X) :=
  TopCat.isoOfHomeo <|
    @Homeomorph.mk (ComplexPoint.Basic.ComplexSchemePoint X) (ComplexPoint.Basic.ComplexSchemePoint X)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.analyticTopology X) ComplexPoint.Basic.Point.analyticTopology
      (Equiv.refl _) (PointTopologies.affineTestToAnalytic_continuous X)
      (PointTopologyEquality.analyticToAffineTest_continuous X)

@[simp]
theorem complexPointSpaceIso_hom_apply (X : _root_.CategoryTheory.Over (Spec (.of ℂ)))
    (z : Betti.Scheme.schemePointSpace X) : (complexPointSpaceIso X).hom z = z := rfl

@[simp]
theorem complexPointSpaceIso_inv_apply (X : _root_.CategoryTheory.Over (Spec (.of ℂ)))
    (z : ComplexPoint.Basic.ComplexSchemePoint X) : (complexPointSpaceIso X).inv z = z := rfl

/-- Equality of the original continuous scheme maps after the identity point comparison. -/
theorem complexPointSpaceIso_naturality {X Y : _root_.CategoryTheory.Over (Spec (.of ℂ))} (f : X ⟶ Y) :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f ≫ (complexPointSpaceIso Y).hom =
      (complexPointSpaceIso X).hom ≫ TopCat.ofHom (ComplexPoint.Basic.Point.continuousMap f) := by
  apply ConcreteCategory.hom_ext
  intro z
  rfl

private theorem complexPointSpaceIso_inv_naturality
    {X Y : _root_.CategoryTheory.Over (Spec (.of ℂ))} (f : X ⟶ Y) :
    (complexPointSpaceIso X).inv ≫ ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map f =
      TopCat.ofHom (ComplexPoint.Basic.Point.continuousMap f) ≫ (complexPointSpaceIso Y).inv := by
  apply ConcreteCategory.hom_ext
  intro z
  rfl

/-- The older actual scheme Betti cohomology agrees with the original singular model. -/
def schemeSingularCohomologyBridgeEquiv (R : Type) [CommRing R]
    (X : _root_.CategoryTheory.Over (Spec (.of ℂ))) (n : ℕ) :
    Betti.Scheme.schemeBetti (ModuleCat.of R R) X n ≃ₗ[R]
      AlgebraicTopology.Singular.CohomologyTo.Cohomology R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n :=
  (((AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyFunctor (ModuleCat.of R R) n).mapIso
    (complexPointSpaceIso X).op).symm.toLinearEquiv).trans
      (SingularCochainBridge.singularCohomologyBridgeEquiv R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n)

/-- The cohomology comparison intertwines actual algebraic pullbacks. -/
theorem schemeSingularCohomologyBridgeEquiv_naturality (R : Type) [CommRing R]
    {X Y : _root_.CategoryTheory.Over (Spec (.of ℂ))} (f : X ⟶ Y) (n : ℕ)
    (c : Betti.Scheme.schemeBetti (ModuleCat.of R R) Y n) :
    schemeSingularCohomologyBridgeEquiv R X n
        (Betti.Scheme.schemeBettiMap (ModuleCat.of R R) n f c) =
      AlgebraicTopology.Singular.CohomologyTo.cohomologyMap R n (TopCat.ofHom (ComplexPoint.Basic.Point.continuousMap f))
        (schemeSingularCohomologyBridgeEquiv R Y n c) := by
  have h :
      Betti.Scheme.schemeBettiMap (ModuleCat.of R R) n f ≫
          AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R)
            (complexPointSpaceIso X).inv n =
        AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R)
            (complexPointSpaceIso Y).inv n ≫
          AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R)
            (TopCat.ofHom (ComplexPoint.Basic.Point.continuousMap f)) n := by
    rw [Betti.Scheme.schemeBettiMap,
      ← AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp,
      ← AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp,
      complexPointSpaceIso_inv_naturality]
  change SingularCochainBridge.singularCohomologyBridgeEquiv R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) n
      ((AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R)
        (complexPointSpaceIso X).inv n)
          (Betti.Scheme.schemeBettiMap (ModuleCat.of R R) n f c)) = _
  have hc := ConcreteCategory.congr_hom h c
  change (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R)
      (complexPointSpaceIso X).inv n)
        (Betti.Scheme.schemeBettiMap (ModuleCat.of R R) n f c) =
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R)
      (TopCat.ofHom (ComplexPoint.Basic.Point.continuousMap f)) n)
        ((AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of R R)
          (complexPointSpaceIso Y).inv n) c) at hc
  rw [hc]
  exact SingularCochainBridge.singularCohomologyBridgeEquiv_naturality R
    (TopCat.ofHom (ComplexPoint.Basic.Point.continuousMap f)) n _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.PointBettiBridge
