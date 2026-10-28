import OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicDeRham.CechScalarCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicCech.ScalarBicomplex

/-! # Cover Scalar Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Rational.CoverScalarIso

noncomputable section

/-! The original all-degree scalar comparison is invertible on any
finite affine cover over rational coefficient rings. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra ℚ R] [Algebra ℚ S] [Module.Flat R S]
  (X : Over (Spec (CommRingCat.of R))) [IsSeparated X.hom]
  (Y : Over (Spec (CommRingCat.of S))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  {ι : Type} [Finite ι] (U : ι → X.left.Opens) (haU : ∀ i, IsAffineOpen (U i))

include haU

omit [Finite ι] in
theorem row_isIso (q : ℕ) : IsIso ((AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.map R S X Y f U hp.w).f q) := by
  change IsIso ((GeometricComparison.IntrinsicCech.ScalarBicomplex.IntrinsicCechScalarBicomplex.map R S X Y f U hp.w).f q)
  exact GeometricComparison.IntrinsicCech.ScalarBicomplex.IntrinsicCechScalarBicomplex.row_isIso R S X Y f U hp haU q

theorem projection_isIso : IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarProjection.BaseIntrinsicCechScalarProjection.map R S X Y f hp.w U) := by
  let (q : ℕ) : IsIso ((AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.map R S X Y f U hp.w).f q) :=
    row_isIso R S X Y f hp U haU q
  let : IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarBicomplex.BaseIntrinsicCechScalarBicomplex.map R S X Y f U hp.w) :=
    HomologicalComplex.Hom.isIso_of_components _
  dsimp only [AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarProjection.BaseIntrinsicCechScalarProjection.map]
  infer_instance

theorem scalarMap_isIso : IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.scalarMap R S X Y f hp.w U) := by
  let := projection_isIso R S X Y f hp U haU
  change IsIso ((AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso (GeometricComparison.FlatScalar.FlatScalarExtension.moduleFunctor R S)
    (AlgebraicGeometry.Crystalline.Cohomology.Cech.Descent.CechDescent.bicomplex R X U)).inv ≫
      (HomologicalComplex₂.totalFunctor (ModuleCat S) (.up ℕ) (.up ℕ) (.up ℕ)).map
        (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarProjection.BaseIntrinsicCechScalarProjection.map R S X Y f hp.w U))
  infer_instance

theorem homologyMap_isIso (q : ℕ) :
    IsIso (AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap R S X Y f hp.w U q) := by
  let := scalarMap_isIso R S X Y f hp U haU
  dsimp only [AlgebraicGeometry.Crystalline.Cohomology.Base.IntrinsicCechScalarTotal.BaseIntrinsicCechScalarTotal.homologyMap]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Rational.CoverScalarIso
