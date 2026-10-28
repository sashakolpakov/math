import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalResidue
import OAI.AlgebraicGeometry.DivisorClass.Chern.WindingCech

/-! # Normal Multiplicity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalMultiplicity.Constructions

noncomputable section

/-!
# DegreeTwo: logarithmic residues of powers of actual normal equations

A local equation raised to an integer power, multiplied by a function with
a continuous logarithm, has that integer times the normal logarithmic residue.
The resulting coefficient uses the proved nonzero universal normal scalar.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.DivisorClass.Chern.WindingCech.RationalCech

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalResidue.Constructions.ExponentialCocycle

variable {M N E : Type} [TopologicalSpace N] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : M → N} {x : M} (P : ComplexPoints.Analytic.NormalPairRecenter.ImmersionNormalPair E ℂ f x)

/-- The already constructed chart Thom class in its literal degree two. -/
def normalChartClass : P.relativeCohomology ExponentialCocycleQ.Constructions.ExponentialCocycle.Q 2 := by
  simpa only [Module.finrank_self, mul_one] using P.rationalClass

theorem normalChartClass_eq_pullback :
    normalChartClass P = P.normalCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q 2 WindingResidue.Constructions.ExponentialCocycle.planeNormalClass := by
  let A : ℕ → ModuleCat.{0} ℚ := fun n => AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane ({0}ᶜ : Set ℂ) n
  let B : ℕ → ModuleCat.{0} ℚ := fun n => P.relativeCohomology ExponentialCocycleQ.Constructions.ExponentialCocycle.Q n
  have transport (i j : ℕ) (h : i = j) (e : A i ≅ ExponentialCocycleQ.Constructions.ExponentialCocycle.Q) :
      cast (congrArg (fun n => (B n : Type)) h)
          (P.normalCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q i (e.inv 1)) =
        P.normalCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q j
          ((cast (congrArg (fun n => A n ≅ ExponentialCocycleQ.Constructions.ExponentialCocycle.Q) h) e).inv 1) := by
    cases h
    rfl
  have hd : 2 * Module.finrank ℂ ℂ = 2 := by simp only [Module.finrank_self, mul_one]
  change cast (congrArg (fun n => (B n : Type)) hd) P.rationalClass =
    P.normalCohomologyMap ExponentialCocycleQ.Constructions.ExponentialCocycle.Q 2
      ((cast (congrArg (fun n => A n ≅ ExponentialCocycleQ.Constructions.ExponentialCocycle.Q) hd)
        (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexTopCohomologyIso ℂ)).inv 1)
  rw [P.rationalClass_eq_pullback]
  exact transport _ _ hd (CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexTopCohomologyIso ℂ)

/-- The logarithmic residue agrees with the existing chart Thom class up to
 the single proved nonzero rational normalization coefficient. -/
theorem normalLogarithmicResidue_eq_chartClass :
    NormalResidue.Constructions.normalLogarithmicResidue P = WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient • normalChartClass P := by
  rw [normalChartClass_eq_pullback]
  exact NormalResidue.Constructions.normalLogarithmicResidue_eq_smul P

/-- Actual integer multiplicity, including negative pole order, is carried
 into genuine relative cohomology by the connecting map. -/
theorem normalEquation_residue_multiplicity
    (s l : C(TopCat.of P.relativeComplement, ℂ)) (hs : ∀ y, s y ≠ 0) (m : ℤ)
    (hsl : ∀ y, s y = Complex.exp (l y) *
      NormalResidue.Constructions.ExponentialCocycle.restrictedFunction P.normalCoordinate P.relativeComplement P.normalCoordinate_mapsTo y ^ m) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting ExponentialCocycleQ.Constructions.ExponentialCocycle.Q (TopCat.of P.neighborhood) P.relativeComplement 1
      (DivisorClass.Chern.WindingCech.RationalCech.logarithmicWindingClass (TopCat.of P.relativeComplement) s hs) =
      ((m : ℚ) * WindingResidue.Constructions.ExponentialCocycle.windingNormalCoefficient) • normalChartClass P := by
  rw [DivisorClass.Chern.WindingCech.RationalCech.logarithmicWindingClass_log_unit_power (TopCat.of P.relativeComplement)
    (NormalResidue.Constructions.ExponentialCocycle.restrictedFunction P.normalCoordinate P.relativeComplement P.normalCoordinate_mapsTo) s l
    (fun y => (NormalResidue.Constructions.ExponentialCocycle.nonzeroRestriction P.normalCoordinate P.relativeComplement
      P.normalCoordinate_mapsTo y).property) hs m hsl, map_zsmul]
  change m • NormalResidue.Constructions.normalLogarithmicResidue P = _
  rw [normalLogarithmicResidue_eq_chartClass]
  rw [← Int.cast_smul_eq_zsmul ℚ m, smul_smul]

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.NormalMultiplicity.Constructions
