import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CrossClassEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProductCohomology

/-! # Continuous Group Pairing -/

namespace OAI.RepresentationTheory.Theta.Geometric.ContinuousGroupPairing

noncomputable section

/-! The original normalized alternating Chern pairing is natural for
continuous maps that commute with the actual group multiplications. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory
open OAI.AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels

variable {X Y : TopCat.{0}}
    (mX : TopCat.of (X × X) ⟶ X) (mY : TopCat.of (Y × Y) ⟶ Y) (f : X ⟶ Y)
    (hm : mX ≫ f = AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, f) : (X, X) ⟶ (Y, Y)) ≫ mY)

include hm in
theorem homologyClassPairing_continuous_naturality
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y 2) (x y : AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossPairing.firstHomology X) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossPairing.homologyClassPairing X mX (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 2 c) x y =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossPairing.homologyClassPairing Y mY c
        (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 1 x)
        (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 1 y) := by
  have hs := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProductCohomology.singularCohomology_commuting_square mX f
    (AlgebraicTopology.Kunneth.ProductModelsAs.Construction.ProductModels.productSpace.map ((f, f) : (X, X) ⟶ (Y, Y))) mY hm 2 c
  rw [← AlgebraicGeometry.AbelianModuli.ReferenceFamily.CrossClassEvaluation.crossClassPairing_multiplication, hs]
  have hn := AlgebraicGeometry.AbelianModuli.ReferenceFamily.CrossClassEvaluation.crossClassPairing_naturality f f
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) mY 2 c) x y
  rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.CrossClassEvaluation.crossClassPairing_multiplication] at hn
  exact hn

include hm in
theorem alternatingClassPairing_continuous_naturality
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) Y 2) (x y : AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossPairing.firstHomology X) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossPairing.alternatingClassPairing X mX (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 2 c) x y =
      AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossPairing.alternatingClassPairing Y mY c
        (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 1 x)
        (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 1 y) := by
  change (1 / 2 : ℚ) * (AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossPairing.homologyClassPairing X mX _ x y - AlgebraicGeometry.AbelianModuli.ReferenceFamily.HomologyCrossPairing.homologyClassPairing X mX _ y x) = _
  rw [homologyClassPairing_continuous_naturality mX mY f hm,
    homologyClassPairing_continuous_naturality mX mY f hm]
  rfl

end

end OAI.RepresentationTheory.Theta.Geometric.ContinuousGroupPairing
