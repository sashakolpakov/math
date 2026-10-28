import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.Serre
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.RefinementTrace

/-! # Pure Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PureTrace

noncomputable section

/-! The normalized trace of a pure coherent sheaf is the top Serre
pairing evaluated on a specified degree-zero class. Actual coherent
maps preserving that class commute with this trace. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable (M : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ = n + 2) (hB : n + 2 ≤ B)
  (c : ℕ) (hM : ∀ q, q ≠ c → (ProjectiveRefinement.Serre.fixedDual M B n hn).ExactAt q)

abbrev cohomology (j : ℕ) : ModuleCat.{u} (TopTracePairing.coefficientRing R) :=
  ProjectiveTower.UnitTrace.cohomology M j

def pairing (i : ℕ) (hi : i + c = n + 1) :=
  ProjectiveTower.UnitTrace.pairing (ProjectiveRefinement.Serre.fixedTower M B n hn)
    B n hn (ProjectiveRefinement.Serre.fixed_above M B n hn) hB c hM i hi

def trace (i : ℕ) (hi : i + c = n + 1) (v : cohomology M 0) :=
  SerreUnitTrace.trace (TopTracePairing.coefficientRing R) (pairing M B n hn hB c hM i hi) v

def traceIso (i : ℕ) (hi : i + c = n + 1)
    (e : (TopTracePairing.coefficientRing R) ≃ₗ[TopTracePairing.coefficientRing R] cohomology M 0) :=
  SerreUnitTrace.traceIso (TopTracePairing.coefficientRing R) (pairing M B n hn hB c hM i hi) e

variable (N : (Proj (homogeneousSubmodule σ R)).Modules)
  [N.IsQuasicoherent] [N.IsFiniteType]
  (hN : ∀ q, q ≠ c → (ProjectiveRefinement.Serre.fixedDual N B n hn).ExactAt q)
  (f : M ⟶ N)

theorem naturality (i : ℕ) (hi : i + c = n + 1) (vM : cohomology M 0) (vN : cohomology N 0)
    (hv : (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) 0).map f vM = vN) :
  let a := NegativeRefinement.leftHom M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f;
  let b := NegativeRefinement.rightHom M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f;
  let : QuasiIso ((Affine.LocalDualInvariance.functor (TopTracePairing.canonicalTwist (R := R) n hn)).map
      a.chainMap.op) := ProjectiveRefinement.DualMap.left_quasiIso M N
        (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (n + 2) hB f;
  let : IsIso (HomologicalComplex.homologyMap
      ((Affine.LocalDualInvariance.functor (TopTracePairing.canonicalTwist (R := R) n hn)).map a.chainMap.op) c) :=
    (isoOfQuasiIsoAt
      ((Affine.LocalDualInvariance.functor (TopTracePairing.canonicalTwist (R := R) n hn)).map a.chainMap.op) c).isIso_hom;
  (Trace.PureFunctorNaturality.cohomologyFunctor
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) i).map
      (Trace.PureRefinement.map (TopTracePairing.canonicalTwist (R := R) n hn) a.chainMap b.chainMap c) ≫
      trace M B n hn hB c hM i hi vM = trace N B n hn hB c hN i hi vN := by
  let a := NegativeRefinement.leftHom M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f
  let b := NegativeRefinement.rightHom M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f
  let : QuasiIso ((Affine.LocalDualInvariance.functor (TopTracePairing.canonicalTwist (R := R) n hn)).map
      a.chainMap.op) := ProjectiveRefinement.DualMap.left_quasiIso M N
        (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (n + 2) hB f
  let : IsIso (HomologicalComplex.homologyMap
      ((Affine.LocalDualInvariance.functor (TopTracePairing.canonicalTwist (R := R) n hn)).map a.chainMap.op) c) :=
    (isoOfQuasiIsoAt
      ((Affine.LocalDualInvariance.functor (TopTracePairing.canonicalTwist (R := R) n hn)).map a.chainMap.op) c).isIso_hom
  exact ProjectiveTower.RefinementTrace.naturality B n hn
    (NegativeRefinement.term_above M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f)
    (ProjectiveRefinement.Serre.fixed_above M B n hn)
    (ProjectiveRefinement.Serre.fixed_above N B n hn) hB c
    (ProjectiveRefinement.Serre.common_exactAt M N B n hn hB c hM f) hM hN
    a b i hi vM vM vN
    (by
      change (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) 0).map (𝟙 M) vM = vM
      rw [CategoryTheory.Functor.map_id]
      rfl)
    hv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PureTrace
