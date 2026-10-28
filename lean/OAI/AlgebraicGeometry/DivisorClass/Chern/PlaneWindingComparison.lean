import OAI.AlgebraicGeometry.DivisorClass.Chern.PrimitiveNormalWinding
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WindingResidue
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalPurityNaturality

/-! # Plane Winding Comparison -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneWindingComparison

noncomputable section

/-!
# ChernClass: identify the two actual normal winding coefficients

The literal complex-plane logarithmic residue used by DegreeTwo and the positive
singular winding used by ChernClass differ by the proved Cech sign. The geometric
normal generators agree under the actual complex-linear coordinate map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WindingResidue.Constructions.ExponentialCocycle

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Evaluate the unique coordinate of the standard normal complex line. -/
def normalLineCoordinateEquiv : (Fin 1 → ℂ) ≃L[ℂ] ℂ :=
  ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ

/-- The finite-dimensional geometric generator uses the same generator
after the actual one-coordinate identification. -/
theorem planeNormalClass_eq_coordinate :
    HodgeConjecture.DegreeTwo.WindingResidue.Constructions.ExponentialCocycle.planeNormalClass = CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass normalLineCoordinateEquiv.symm := by
  have transport (n : ℕ) (hn : Module.finrank ℂ ℂ = n)
      (e : ℂ ≃L[ℂ] (Fin n → ℂ)) :
      (cast (congrArg (fun j => CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexLocalCohomology ℂ (2 * j) ≅ ModuleCat.of ℚ ℚ) hn)
        (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexTopCohomologyIso ℂ)).inv 1 = CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.complexCoordinateLocalClass e := by
    subst n
    exact CycleClass.Geometric.ComplexLocalPurityNaturality.Cycles.finiteComplexLocalClass_eq_of_coordinates ℂ e
  exact transport 1 (Module.finrank_self ℂ) normalLineCoordinateEquiv.symm

theorem planeNormalClass_pullback :
    (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso normalLineCoordinateEquiv 2).hom HodgeConjecture.DegreeTwo.WindingResidue.Constructions.ExponentialCocycle.planeNormalClass =
      CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1 := by
  rw [planeNormalClass_eq_coordinate]
  change (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso normalLineCoordinateEquiv.symm 2).inv
    ((CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso normalLineCoordinateEquiv.symm 2).hom
      (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1)) = CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass 1
  exact Iso.hom_inv_id_apply _ _

/-- The two original winding classes have exactly the previously proved
logarithmic-versus-singular sign. -/
theorem planeWindingResidue_pullback :
    (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso normalLineCoordinateEquiv 2).hom HodgeConjecture.DegreeTwo.WindingResidue.Constructions.ExponentialCocycle.windingResidueClass =
      -NormalWinding.normalSupportedWindingClass := by
  have hw : HodgeConjecture.DegreeTwo.WindingResidue.Constructions.ExponentialCocycle.windingResidueClass = -Supported.Winding.supportedWindingClass HodgeConjecture.DegreeTwo.ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane ({0}ᶜ : Set ℂ)
      WindingLoop.puncturedCoordinate WindingLoop.puncturedCoordinate_ne_zero := by
    unfold HodgeConjecture.DegreeTwo.WindingResidue.Constructions.ExponentialCocycle.windingResidueClass HodgeConjecture.DegreeTwo.WindingNormalization.Constructions.ExponentialCocycle.universalWindingClass
    rw [WindingComparisonD.RationalCech.logarithmicWindingClass_eq_neg_singularWindingClass, map_neg]
    rfl
  rw [hw, map_neg]
  congr 1
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearTopIso normalLineCoordinateEquiv).hom
    (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearEquiv_mapsTo_puncture normalLineCoordinateEquiv) 2
    (Supported.Winding.supportedWindingClass HodgeConjecture.DegreeTwo.ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane ({0}ᶜ : Set ℂ) WindingLoop.puncturedCoordinate WindingLoop.puncturedCoordinate_ne_zero) = _
  rw [Supported.Winding.supportedWindingClass_pullback]
  rfl

/-- Both independently constructed coefficients agree with the proved
sign, after transporting their actual normal spaces. -/
theorem windingNormalCoefficient_eq_neg_normalWindingCoefficient :
    HodgeConjecture.DegreeTwo.WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient = -NormalWinding.normalWindingCoefficient := by
  have h := congrArg (fun a =>
    (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.complexLinearLocalCohomologyIso normalLineCoordinateEquiv 2).hom a)
    HodgeConjecture.DegreeTwo.WindingResidue.Constructions.ExponentialCocycle.windingResidueClass_eq_smul_normal
  rw [planeWindingResidue_pullback, map_smul, planeNormalClass_pullback] at h
  have hc := congrArg (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyEquiv 1) h
  rw [map_neg, map_smul, CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass_normalization] at hc
  change -NormalWinding.normalWindingCoefficient = HodgeConjecture.DegreeTwo.WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient * 1 at hc
  exact (hc.trans (mul_one _)).symm

theorem neg_windingNormalCoefficient_eq_normalWindingCoefficient :
    -HodgeConjecture.DegreeTwo.WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient = NormalWinding.normalWindingCoefficient := by
  rw [windingNormalCoefficient_eq_neg_normalWindingCoefficient, neg_neg]

/-- The DegreeTwo plane coefficient is also a primitive integral sign. -/
theorem planeWindingNormalCoefficient_eq_one_or_neg_one :
    HodgeConjecture.DegreeTwo.WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient = 1 ∨ HodgeConjecture.DegreeTwo.WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient = -1 := by
  rw [windingNormalCoefficient_eq_neg_normalWindingCoefficient]
  rcases PrimitiveNormalWinding.normalWindingCoefficient_eq_one_or_neg_one with h | h
  · exact Or.inr (congrArg Neg.neg h)
  · exact Or.inl (by rw [h, neg_neg])

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneWindingComparison
