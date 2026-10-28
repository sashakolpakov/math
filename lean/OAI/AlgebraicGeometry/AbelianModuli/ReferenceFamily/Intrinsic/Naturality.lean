import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodSquares
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticePeriodEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProductCohomology

/-! # Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Naturality.IntrinsicRationalPeriods

noncomputable section

/-! Algebraic maps act on native singular H1 by the dual of their
constructed rational period lift. This follows from the actual covering
square and normalized period characters, with no comparison input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodSquares.IntrinsicLinearMaps

theorem nativeH1Periods_lattice (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (c : A.variety.rationalCohomology 1)
    (ell : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A c (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ell) =
      HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
        (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff (PeriodSquares.IntrinsicLinearMaps.nativePeriodMap A) 1 c) ell :=
  LatticePeriodEvaluation.LatticeCharacters.singularH1LatticeDualEquiv_lattice (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff (PeriodSquares.IntrinsicLinearMaps.nativePeriodMap A) 1 c) ell

theorem nativeH1Periods_naturality {A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (f : A.toOver ⟶ B.toOver) [IsMonHom f]
    (c : B.variety.rationalCohomology 1) :
    HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff
      (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)) 1 c) =
      (HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods B c).comp (IntegralMaps.IntrinsicLinearMaps.rationalLift f) := by
  apply LatticePeriodEvaluation.LatticeCharacters.characterRestriction_injective (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
  apply AddMonoidHom.ext
  intro ell
  let mu : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B := ⟨Maps.IntrinsicLinearMaps.linearLift f ell.val, Maps.IntrinsicLinearMaps.linearLift_preserves f ell.val ell.property⟩
  have hs := ProductCohomology.singularCohomology_commuting_square (PeriodSquares.IntrinsicLinearMaps.nativePeriodMap A)
    (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)) (PeriodSquares.IntrinsicLinearMaps.nativeTorusPointMap f) (PeriodSquares.IntrinsicLinearMaps.nativePeriodMap B)
    (PeriodSquares.IntrinsicLinearMaps.nativePeriod_map_square f) 1 c
  have hper := SingularPeriodEquiv.cohomologyPeriod_pullback (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B)
    (PeriodSquares.IntrinsicLinearMaps.nativeCoverLinearMap f) (PeriodSquares.IntrinsicLinearMaps.nativeTorusPointMap f) (PeriodSquares.IntrinsicLinearMaps.nativeCover_period_square f)
    (PeriodSquares.IntrinsicLinearMaps.nativeCoverLinearMap_zero f)
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff (PeriodSquares.IntrinsicLinearMaps.nativePeriodMap B) 1 c) ell mu rfl
  have hleft := nativeH1Periods_lattice A
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)) 1 c) ell
  have hright := nativeH1Periods_lattice B c mu
  exact hleft.trans ((congrArg (fun c => HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) c ell) hs).trans
    (hper.trans hright.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Naturality.IntrinsicRationalPeriods
