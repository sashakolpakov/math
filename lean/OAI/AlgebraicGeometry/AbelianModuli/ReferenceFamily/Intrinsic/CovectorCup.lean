import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AmpleChernInvariant
import OAI.AlgebraicGeometry.AbelianVariety.GeometricCup
import OAI.AlgebraicGeometry.AbelianVariety.ExteriorCohomologyComplexCup

/-! # Covector Cup -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CovectorCup

noncomputable section

/-! The identity-covector comparison preserves the actual cup product.
The native preferred tangent chart has identity differential. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

theorem nativeInvariantChartEval (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    AbelianVariety.PureAverage.Constructions.ExteriorCohomology.invariantChartEvalEquiv (E := A.variety.analyticModel) (G := A.variety.analyticSpace) n =
      AbelianVariety.InvariantClosed.Constructions.ExteriorCohomology.invariantFormsEvalEquiv (E := A.variety.analyticModel) (G := A.variety.analyticSpace) n := by
  ext a v
  change a.val 1 (fun i => (Analysis.DifferentialForms.Manifold.TangentCoordinates.preferredTangentEquiv (E := A.variety.analyticModel)
    (1 : A.variety.analyticSpace)).symm (v i)) = a.val 1 v
  exact congrArg (a.val 1) (funext (fun i => Holomorphic.TangentMaps.preferredTangent_inverse_identity
    (1 : A.variety.analyticSpace) (v i)))

theorem nativeModelCovectorBettiEquiv (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (n : ℕ) :
    AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A n = AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A n := by
  unfold AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv
  rw [nativeInvariantChartEval]
  rfl

theorem nativeCovectorBetti_cup (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (p q : ℕ)
    (a : A.variety.complexCohomology p) (b : A.variety.complexCohomology q) :
    (AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A (p + q)).symm
      (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (Betti.Scheme.schemePointSpace A.toOver) p q a b) =
    AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge ((AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A p).symm a)
      ((AbelianVariety.DeRham.Constructions.ExteriorCohomology.abelianCovectorBettiEquiv A q).symm b) := by
  rw [← AbelianVariety.GeometricCup.Constructions.ExteriorCohomology.geometricBettiWedge_eq_cup, AbelianVariety.GeometricProduct.Constructions.ExteriorCohomology.geometricBettiWedge,
    nativeModelCovectorBettiEquiv, nativeModelCovectorBettiEquiv, nativeModelCovectorBettiEquiv,
    LinearEquiv.symm_apply_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.CovectorCup
