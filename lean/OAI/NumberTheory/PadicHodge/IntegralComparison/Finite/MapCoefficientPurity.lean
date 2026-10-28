import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.CoefficientPurity
import OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.MapPureTrace

/-! # Map Coefficient Purity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.MapCoefficientPurity

noncomputable section

/-! The finite-coefficient purity hypothesis of native Serre trace
naturality follows from the original finite flat geometry. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.StructurePullbackUnit OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

variable {Y X : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Flat f]
  (i : X ⟶ Proj (homogeneousSubmodule σ R)) [IsClosedImmersion i]
  (B n : ℕ) (hn : Fintype.card σ = n + 2) (hB : n + 2 ≤ B)
  (g : ℕ) [SmoothOfRelativeDimension g (i ≫ AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ)]

local instance : (Cech.StructurePullbackUnit.coefficients f i).IsQuasicoherent :=
  MapPureTrace.coefficients_quasicoherent f i
local instance : (Cech.StructurePullbackUnit.coefficients f i).IsFiniteType :=
  MapPureTrace.coefficients_finiteType f i

include hB in
theorem exactAt (q : ℕ) (hq : q ≠ n + 1 - g) :
    (ProjectiveRefinement.Serre.fixedDual (Cech.StructurePullbackUnit.coefficients f i) B n hn).ExactAt q := by
  exact ProjectiveFinite.CoefficientPurity.exactAt f i
    (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn)
    B (n + 2) hB g q (by omega)

variable [Module.Injective R R] [Nonempty X]

theorem naturality :
    let M := Projective.ClosedImmersionPurity.directImage i;
    let C := Cech.StructurePullbackUnit.coefficients f i;
    let hM := Smooth.ProjectiveSerre.exactAt i B n hn hB g;
    let hdim : g + (n + 1 - g) = n + 1 := by
      have h := Smooth.ClosedDimension.projective i g
      omega;
    let vM := Cech.StructureUnit.unit i (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ));
    let vC := Cech.StructurePullbackUnit.unit f i (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.iSup_coordinateOpenCover_eq_top (R := R) (σ := σ));
    let a := Projective.NegativeRefinement.leftHom M C (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (Cech.StructurePullbackUnit.sheafMap f i);
    let b := Projective.NegativeRefinement.rightHom M C (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (Cech.StructurePullbackUnit.sheafMap f i);
    let : QuasiIso ((Affine.LocalDualInvariance.functor (Projective.TopTracePairing.canonicalTwist (R := R) n hn)).map
      a.chainMap.op) := ProjectiveRefinement.DualMap.left_quasiIso M C
        (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (n + 2) hB (Cech.StructurePullbackUnit.sheafMap f i);
    let : IsIso (HomologicalComplex.homologyMap
      ((Affine.LocalDualInvariance.functor (Projective.TopTracePairing.canonicalTwist (R := R) n hn)).map a.chainMap.op) (n + 1 - g)) :=
      (isoOfQuasiIsoAt
        ((Affine.LocalDualInvariance.functor (Projective.TopTracePairing.canonicalTwist (R := R) n hn)).map a.chainMap.op) (n + 1 - g)).isIso_hom;
    (Trace.PureFunctorNaturality.cohomologyFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) g).map
        (Trace.PureRefinement.map (Projective.TopTracePairing.canonicalTwist (R := R) n hn) a.chainMap b.chainMap (n + 1 - g)) ≫
      Projective.PureTrace.trace M B n hn hB (n + 1 - g) hM g hdim vM =
      Projective.PureTrace.trace C B n hn hB (n + 1 - g) (exactAt f i B n hn hB g) g hdim vC := by
  exact MapPureTrace.naturality f i B n hn hB g
    (exactAt f i B n hn hB g)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.MapCoefficientPurity
