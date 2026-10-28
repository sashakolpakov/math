import OAI.AlgebraicGeometry.AbelianVariety.InvariantWedge
import OAI.AlgebraicGeometry.AbelianVariety.HodgeCharacters
import OAI.AlgebraicTopology.Kunneth.ClosedManifoldWedge
import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

/-! # Geometric Product -/

namespace OAI.AlgebraicGeometry.AbelianVariety.GeometricProduct.Constructions.ExteriorCohomology

noncomputable section

section

open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions

def abelianClosedRepresentative (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (a : A.variety.complexCohomology n) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms A.variety.analyticModel A.variety.analyticSpace n :=
  InvariantCohomology.Constructions.Exterior.invariantClosedInclusion n
    ((PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv (E := A.variety.analyticModel) (G := A.variety.analyticSpace) n).symm
      ((PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A n).symm a))

theorem abelianClosedRepresentative_class (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ)
    (a : A.variety.complexCohomology n) :
    (A.variety.deRhamBettiIso n).hom (A.variety.deRhamClass n (abelianClosedRepresentative A n a)) =
      a :=
  (PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A n).apply_symm_apply a

/-- Exterior multiplication of the unique invariant representatives, transported by actual integration. -/
def geometricBettiWedge (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p q : ℕ)
    (a : A.variety.complexCohomology p) (b : A.variety.complexCohomology q) :
    A.variety.complexCohomology (p + q) :=
  PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A (p + q)
    (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge ((PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A p).symm a)
      ((PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A q).symm b))

theorem geometricBettiWedge_closedForm (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p q : ℕ)
    (a : A.variety.complexCohomology p) (b : A.variety.complexCohomology q) :
    geometricBettiWedge A p q a b =
      (A.variety.deRhamBettiIso (p + q)).hom
        (A.variety.deRhamClass (p + q)
          (AlgebraicTopology.Kunneth.ClosedManifoldWedge.Constructions.closedManifoldWedge (abelianClosedRepresentative A p a) (abelianClosedRepresentative A q b))) := by
  change (A.variety.deRhamBettiIso (p + q)).hom
    (InvariantCohomology.Constructions.Exterior.invariantDeRham (p + q)
      ((PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv (p + q)).symm
        (AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge ((PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A p).symm a)
          ((PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A q).symm b)))) = _
  rw [InvariantWedge.Constructions.ExteriorCohomology.invariantChartEval_symm_wedge]
  rfl

theorem bettiScalarAction_geometricWedge (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p q : ℕ) (z : ℂˣ)
    (a : A.variety.complexCohomology p) (b : A.variety.complexCohomology q) :
    HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction A (p + q) z (geometricBettiWedge A p q a b) =
      geometricBettiWedge A p q (HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction A p z a) (HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction A q z b) := by
  simp only [HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction, geometricBettiWedge, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, InvariantWedge.Constructions.ExteriorCohomology.scalarCovectorPullback_wedge]

theorem bettiScalarAction_zero (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (z : ℂˣ)
    (a : A.variety.complexCohomology 0) : HodgeCharacters.Constructions.ExteriorCohomology.bettiScalarAction A 0 z a = a := by
  let e := PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A 0
  have he : Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback A.variety.analyticModel 0 z (e.symm a) = e.symm a := by
    ext v
    change (e.symm a) (fun i => (z : ℂ) • v i) = (e.symm a) v
    exact congrArg (e.symm a) (Subsingleton.elim _ _)
  change e (Analysis.DifferentialForms.Manifold.Bidegree.scalarCovectorPullback A.variety.analyticModel 0 z (e.symm a)) = a
  rw [he, e.apply_symm_apply]

end

open _root_.CategoryTheory
open OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality

variable {R : Type} [CommRing R]

theorem simplicialCohomologyPullback_cup {K L : SSet.{0}} (f : K ⟶ L) (p q : ℕ)
    (a : (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains L (ModuleCat.of R R)).homology p)
    (b : (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains L (ModuleCat.of R R)).homology q) :
    HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of R R) f) (p + q)
      (AlgebraicTopology.Products.CupCohomology.cohomologyCup L p q a b) = AlgebraicTopology.Products.CupCohomology.cohomologyCup K p q
        (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of R R) f) p a)
        (HomologicalComplex.homologyMap (AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of R R) f) q b) := by
  obtain ⟨c, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective _ p a
  obtain ⟨d, rfl⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective _ q b
  rw [AlgebraicTopology.Products.CupCohomology.cohomologyCupWith_class_class, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality,
    AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, AlgebraicTopology.Products.CupCohomology.cohomologyCupWith_class_class]
  apply congrArg (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K (ModuleCat.of R R)) (p + q))
  apply Subtype.ext
  exact AlgebraicTopology.Products.Cup.cupWith_pullback f (L := ModuleCat.of R R) (LinearMap.mul R R) c.val d.val

theorem bettiToSmoothSingular_cup (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (a : V.complexCohomology p) (b : V.complexCohomology q) :
    V.bettiToSmoothSingular (p + q) (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace V.toOver) p q a b) =
      AlgebraicTopology.Products.CupCohomology.cohomologyCup (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex V.analyticModel V.analyticSpace).toSSet p q
        (V.bettiToSmoothSingular p a) (V.bettiToSmoothSingular q b) :=
  simplicialCohomologyPullback_cup (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion V.analyticModel V.analyticSpace) p q a b

theorem bettiToSmoothSingular_injective (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    Function.Injective (V.bettiToSmoothSingular n) := by
  have : IsIso (V.bettiToSmoothSingular n) := by
    change IsIso (HomologicalComplex.homologyMap V.bettiRestrictionCochain n)
    infer_instance
  exact (asIso (V.bettiToSmoothSingular n)).toLinearEquiv.injective

end

end OAI.AlgebraicGeometry.AbelianVariety.GeometricProduct.Constructions.ExteriorCohomology
