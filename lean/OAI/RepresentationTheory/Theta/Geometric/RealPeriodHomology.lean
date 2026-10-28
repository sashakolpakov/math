import OAI.RepresentationTheory.Theta.Geometric.RealPeriodCoe
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality

/-! # Real Period Homology -/

namespace OAI.RepresentationTheory.Theta.Geometric.RealPeriodHomology

noncomputable section

/-! Native singular periods and homology commute with continuous maps
that have the specified actual real linear lift of exponential coverings. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

namespace RealPeriodMaps
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyNaturality.IntrinsicRationalPeriods

local instance realPeriodHomology_integral (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property

variable {A B : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety} (T : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A →L[ℝ] AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel B)
    (hT : ∀ v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A, T v ∈ AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B)
    (f : AlgebraicGeometry.Betti.Scheme.schemePointSpace A.toOver ⟶ AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver)
    (hf : ∀ v : AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A,
      f (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input A (QuotientAddGroup.mk v)) =
        AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodHomeomorph AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Torsion.IntrinsicTorsion.e06Input B (QuotientAddGroup.mk (T v)))

include hf in
theorem nativeH1_naturality (c : B.variety.rationalCohomology 1) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff f 1 c) =
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods B c).comp (RealPeriodCoe.RealPeriodMaps.rationalMap T hT) := by
  apply AlgebraicGeometry.AbelianModuli.ReferenceFamily.LatticePeriodEvaluation.LatticeCharacters.characterRestriction_injective (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
  apply AddMonoidHom.ext
  intro ell
  let mu : AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B := ⟨T ell.val, hT ell.val ell.property⟩
  have hs := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ProductCohomology.singularCohomology_commuting_square (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodSquares.IntrinsicLinearMaps.nativePeriodMap A)
    f (RealPeriodCoe.RealPeriodMaps.torusMap f) (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodSquares.IntrinsicLinearMaps.nativePeriodMap B) (RealPeriodCoe.RealPeriodMaps.period_square f) 1 c
  have hper := AlgebraicGeometry.AbelianModuli.ReferenceFamily.SingularPeriodEquiv.cohomologyPeriod_pullback (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice B)
    (RealPeriodCoe.RealPeriodMaps.coverMap T) (RealPeriodCoe.RealPeriodMaps.torusMap f) (RealPeriodCoe.RealPeriodMaps.cover_square T f hf) T.map_zero
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodSquares.IntrinsicLinearMaps.nativePeriodMap B) 1 c) ell mu rfl
  have hleft := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Naturality.IntrinsicRationalPeriods.nativeH1Periods_lattice A (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Coeff f 1 c) ell
  have hright := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.Naturality.IntrinsicRationalPeriods.nativeH1Periods_lattice B c mu
  exact hleft.trans ((congrArg (fun c => AlgebraicGeometry.HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod (AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) c ell) hs).trans
    (hper.trans hright.symm))

include hf in
theorem nativeHomology_naturality (v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RationalPeriods.IntrinsicRationalPeriods.rationalPeriods A) :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B (RealPeriodCoe.RealPeriodMaps.rationalMap T hT v) =
      AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 1 (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A v) := by
  apply (Module.evalEquiv ℚ (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.rationalHomologyOne B)).injective
  apply LinearMap.ext
  intro φ
  obtain ⟨c, rfl⟩ := (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := ℚ) (AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver) 1).surjective φ
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver) 1 c
      (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods B (RealPeriodCoe.RealPeriodMaps.rationalMap T hT v)) =
    AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (AlgebraicGeometry.Betti.Scheme.schemePointSpace B.toOver) 1 c
      (AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℚ) f 1 (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A v))
  have h := LinearMap.congr_fun (nativeH1_naturality T hT f hf c) v
  have ha := AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods_pairing A v (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) f 1 c)
  have hn := AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality (ModuleCat.of ℚ ℚ) f 1 c (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods A v)
  exact (AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.HomologyPeriods.IntrinsicRationalPeriods.nativeHomologyPeriods_pairing B (RealPeriodCoe.RealPeriodMaps.rationalMap T hT v) c).trans
    (h.symm.trans (ha.symm.trans hn))

end RealPeriodMaps

end

end OAI.RepresentationTheory.Theta.Geometric.RealPeriodHomology
