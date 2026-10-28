import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicOrdered.CechTransferCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TotalUnitMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveRefinement.AffineTerms

/-! # Total Unit Coordinates -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TotalUnitCoordinates

noncomputable section

/-! The original projective total-unit map is the original ordered
Čech right map followed by the inverse of the left refinement map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TopTracePairing OAI.NumberTheory.PadicHodge.IntegralComparison.NegativeTwistResidueNaturality
open OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveTower.UnitTrace (cohomology)

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
  {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

variable (M N : (Proj (homogeneousSubmodule σ R)).Modules)
  [M.IsQuasicoherent] [M.IsFiniteType] [N.IsQuasicoherent] [N.IsFiniteType]
  (B n : ℕ) (hn : Fintype.card σ = n + 2) (hB : n + 2 ≤ B) (f : M ⟶ N)

local instance projectiveSeparated : (Proj (homogeneousSubmodule σ R)).IsSeparated := by
  constructor
  rw [← terminal.comp_from (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))]
  infer_instance

theorem left : TotalUnitMap.left M N B n hn f =
    (IntrinsicOrdered.CechTransferCoordinates.Intrinsic.nativeFunctor
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (n + 1)).map
      (ProjectiveRefinement.DualMap.leftMap M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (n + 2) f) := rfl

theorem right : TotalUnitMap.right M N B n hn f =
    (IntrinsicOrdered.CechTransferCoordinates.Intrinsic.nativeFunctor
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ)) (n + 1)).map
      (ProjectiveRefinement.DualMap.rightMap M N (NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn) B (n + 2) f) := rfl

def nativeMap := by
  let j := NegativeTwistResidueNaturality.topChart.{u} (n + 1) hn
  letI : ∀ q, (((ProjectiveRefinement.DualMap.dualFunctor (R := R) j (n + 2)).obj
      (op (NegativeResolution.complex M j B))).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.fixed_dual_qc M j B (n + 2) hB
  letI : ∀ q, (((ProjectiveRefinement.DualMap.dualFunctor (R := R) j (n + 2)).obj
      (op (NegativeRefinement.complex M N j B f))).X q).IsQuasicoherent :=
    ProjectiveRefinement.AffineTerms.common_dual_qc M N j B (n + 2) hB f
  letI := ProjectiveRefinement.DualMap.left_quasiIso M N j B (n + 2) hB f
  exact IntrinsicOrdered.CechTransferCoordinates.Intrinsic.nativeMap
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
    (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover_isAffineOpen (R := R)) (n + 1)
    (ProjectiveRefinement.DualMap.leftMap M N j B (n + 2) f)
    (ProjectiveRefinement.DualMap.rightMap M N j B (n + 2) f)

variable [Module.Injective R R]
  (eM : TopTracePairing.coefficientRing R ≃ₗ[TopTracePairing.coefficientRing R] ProjectiveTower.UnitTrace.cohomology M 0)

theorem nativeMap_eq : nativeMap M N B n hn hB f =
    TotalUnitMap.map M N B n hn hB f eM := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TotalUnitCoordinates
