import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.Serre
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PureTrace
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.FactorizationCoordinates

/-! # Pure Factorization Trace -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PureFactorizationTrace

noncomputable section

/-! The original pure coherent trace is natural along any actual dual map
satisfying the common-resolution square and preserving the specified unit class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PureTrace

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  {σ : Type} [Fintype σ] [LinearOrder σ]

attribute [local instance] MvPolynomial.gradedAlgebra

variable (M : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ = n + 2) (hB : n + 2 ≤ B)
  (c : ℕ) (hM : ∀ q, q ≠ c → (ProjectiveRefinement.Serre.fixedDual M B n hn).ExactAt q)

variable (N : (Proj (homogeneousSubmodule σ R)).Modules)
  [N.IsQuasicoherent] [N.IsFiniteType]
  (hN : ∀ q, q ≠ c → (ProjectiveRefinement.Serre.fixedDual N B n hn).ExactAt q)
  (f : M ⟶ N)

theorem naturality
    (m : (ProjectiveRefinement.Serre.fixedDual N B n hn).homology c ⟶
      (ProjectiveRefinement.Serre.fixedDual M B n hn).homology c)
    (hm : m ≫ HomologicalComplex.homologyMap
        ((Affine.LocalDualInvariance.functor (TopTracePairing.canonicalTwist (R := R) n hn)).map
          (NegativeRefinement.leftHom M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f).chainMap.op) c =
      HomologicalComplex.homologyMap
        ((Affine.LocalDualInvariance.functor (TopTracePairing.canonicalTwist (R := R) n hn)).map
          (NegativeRefinement.rightHom M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f).chainMap.op) c)
    (i : ℕ) (hi : i + c = n + 1) (vM : PureTrace.cohomology M 0) (vN : PureTrace.cohomology N 0)
    (hv : (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) 0).map f vM = vN) :
    (ProjectiveRefinement.Serre.cohomologyFunctor (R := R) (σ := σ) i).map m ≫
        PureTrace.trace M B n hn hB c hM i hi vM =
      PureTrace.trace N B n hn hB c hN i hi vN := by
  let a := NegativeRefinement.leftHom M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f
  let b := NegativeRefinement.rightHom M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f
  exact ProjectiveTower.FactorizationCoordinates.naturality B n hn
    (NegativeRefinement.term_above M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B f)
    (ProjectiveRefinement.Serre.fixed_above M B n hn)
    (ProjectiveRefinement.Serre.fixed_above N B n hn) hB c
    (ProjectiveRefinement.Serre.common_exactAt M N B n hn hB c hM f) hM hN
    a b m hm i hi vM vM vN
    (by
      change (TopCechRightExact.functor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) 0).map (𝟙 M) vM = vM
      rw [CategoryTheory.Functor.map_id]
      rfl)
    hv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.PureFactorizationTrace
