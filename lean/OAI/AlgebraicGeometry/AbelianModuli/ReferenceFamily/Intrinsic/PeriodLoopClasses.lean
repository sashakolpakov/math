import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.Loop

/-! # Period Loop Classes -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodLoopClasses

noncomputable section

/-! The original period loops on the original abelian point space are
based at its identity and compute the native H¹ period marking. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped Simplicial _root_.Manifold ContDiff _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : CommGroup (Betti.Scheme.schemePointSpace A.toOver) :=
  inferInstanceAs (CommGroup A.variety.analyticSpace)
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth
local instance (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    LieGroup (𝓘(ℝ, A.variety.analyticModel)) ∞ A.variety.analyticSpace :=
  HodgeConjecture.DegreeTwo.IntrinsicProductMaps.Constructions.IntrinsicAbelianLieGroup.realLieGroup A

def nativePeriodLoop (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (ℓ : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace A.toOver)) _⦋1⦌ :=
  (TopCat.toSSet.map (PeriodSquares.IntrinsicLinearMaps.nativePeriodMap A)).app (op ⦋1⦌)
    (Integral.Loop.latticePeriodLoop (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ)

theorem nativePeriodLoop_closed (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (ℓ : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace A.toOver)).δ 0 (nativePeriodLoop A ℓ) =
      (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace A.toOver)).δ 1 (nativePeriodLoop A ℓ) := by
  unfold nativePeriodLoop
  rw [← SSet.δ_naturality_apply, ← SSet.δ_naturality_apply, Integral.Loop.latticePeriodLoop_closed]

theorem nativePeriodMap_zero (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) :
    PeriodSquares.IntrinsicLinearMaps.nativePeriodMap A (0 : HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.Base (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)) = 1 := by
  let : ConnectedSpace A.variety.analyticSpace := HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.native_connectedSpace Torsion.IntrinsicTorsion.e06Input A
  change HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expQuotientHomeomorph (C := A.variety.analyticSpace)
    (QuotientAddGroup.mk (0 : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) = 1
  rw [HodgeConjecture.DegreeTwo.ExponentialLocal.Constructions.Exponential.expQuotientHomeomorph_mk]
  exact HodgeConjecture.DegreeTwo.ExponentialM.Constructions.Exponential.exp_zero (G := A.variety.analyticSpace)

theorem nativePeriodLoop_basepoint (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (ℓ : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    TopCat.toSSetObj₀Equiv
      ((TopCat.toSSet.obj (Betti.Scheme.schemePointSpace A.toOver)).δ 1 (nativePeriodLoop A ℓ)) = 1 := by
  rw [← TopCat.toSSetObj₁Equiv_apply_zero]
  have he (t : TopCat.I) : TopCat.toSSetObj₁Equiv (nativePeriodLoop A ℓ) t =
      PeriodSquares.IntrinsicLinearMaps.nativePeriodMap A (HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.projection (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)
        (TopCat.toSSetObj₁Equiv (HodgeConjecture.DegreeTwo.PeriodEdges.Constructions.SingularPeriods.vectorEdge (ℓ : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A)) t)) := rfl
  rw [he, HodgeConjecture.DegreeTwo.PeriodEdges.Constructions.SingularPeriods.vectorEdge_zero]
  exact nativePeriodMap_zero A

theorem nativePeriodLoop_cocycle_evaluation (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace A.toOver) 1)
    (ℓ : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    AlgebraicTopology.Cohomology.Singular.Coefficients.simplicialEvaluation (TopCat.toSSet.obj (Betti.Scheme.schemePointSpace A.toOver)) (ModuleCat.of ℚ ℚ)
        (nativePeriodLoop A ℓ) c.val =
      HomologyPeriods.IntrinsicRationalPeriods.nativeH1Periods A (AlgebraicTopology.Cohomology.Singular.Representatives.singularClass (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace A.toOver) 1 c)
        (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ) := by
  rw [Naturality.IntrinsicRationalPeriods.nativeH1Periods_lattice, AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.singularCohomologyPullback_class, HodgeConjecture.DegreeTwo.SingularPeriodsD.Constructions.SingularPeriods.cohomologyPeriod_class]
  rw [HodgeConjecture.DegreeTwo.PeriodEdges.Constructions.SingularPeriods.periodHom_eq_edge_evaluation (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) _ ℓ (HodgeConjecture.DegreeTwo.PeriodEdges.Constructions.SingularPeriods.vectorEdge (ℓ : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A))
    (HodgeConjecture.DegreeTwo.PeriodEdges.Constructions.SingularPeriods.vectorEdge_zero _) (HodgeConjecture.DegreeTwo.PeriodEdges.Constructions.SingularPeriods.vectorEdge_one _)]
  exact (AlgebraicTopology.Cohomology.Singular.Formulas.evaluation_pullback_apply (ModuleCat.of ℚ ℚ) (TopCat.toSSet.map (PeriodSquares.IntrinsicLinearMaps.nativePeriodMap A))
    c.val (Integral.Loop.latticePeriodLoop (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.PeriodLoopClasses
