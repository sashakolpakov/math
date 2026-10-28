import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WindingNormalization
import OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity

/-! # Winding Residue -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WindingResidue.Constructions.ExponentialCocycle

noncomputable section

/-!
# DegreeTwo: the logarithmic winding residue is a genuine nonzero normal generator

The actual connecting homomorphism for the punctured complex plane sends the
constructed winding class to a nonzero relative class. Its relation to the
existing normal-class normalization is an actual nonzero rational scalar,
computed through the existing local-cohomology isomorphism.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity.Cycles

/-- The actual connecting map is invertible because the complex plane is contractible. -/
def windingConnectingIso :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Punctured 1 ≅ AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane ({0}ᶜ : Set ℂ) 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnectingIso ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane ({0}ᶜ : Set ℂ) 1
    (AlgebraicTopology.Cohomology.Singular.Contractible.isZero_singularCohomology_of_contractible ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane 1 (by decide))
    (AlgebraicTopology.Cohomology.Singular.Contractible.isZero_singularCohomology_of_contractible ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane 2 (by decide))

/-- The actual exponential-sequence winding class, mapped into normal relative cohomology. -/
def windingResidueClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane ({0}ᶜ : Set ℂ) 2 :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeCohomologyConnecting ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane ({0}ᶜ : Set ℂ) 1 WindingNormalization.Constructions.ExponentialCocycle.universalWindingClass

theorem windingResidueClass_ne_zero : windingResidueClass ≠ 0 := by
  intro hz
  apply WindingNormalization.Constructions.ExponentialCocycle.universalWindingClass_ne_zero
  apply windingConnectingIso.toLinearEquiv.injective
  change windingConnectingIso.hom WindingNormalization.Constructions.ExponentialCocycle.universalWindingClass = windingConnectingIso.hom 0
  rw [map_zero]
  exact hz

/-- The existing finite-complex normal isomorphism in the literal degree two. -/
def planeNormalIso : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane ({0}ᶜ : Set ℂ) 2 ≅ ExponentialCocycleQ.Constructions.ExponentialCocycle.Q := by
  simpa only [Module.finrank_self, mul_one] using CycleClass.Geometric.FiniteComplexLocalPurity.Cycles.finiteComplexTopCohomologyIso ℂ

/-- The existing finite-complex local class, transported only across its degree equality. -/
def planeNormalClass : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane ({0}ᶜ : Set ℂ) 2 :=
  planeNormalIso.inv 1

theorem planeNormalClass_normalization : planeNormalIso.hom planeNormalClass = 1 :=
  planeNormalIso.inv_hom_id_apply 1

/-- The actual rational scalar between the logarithmic residue and the fixed normal class. -/
def windingNormalCoefficient : ℚ := planeNormalIso.hom windingResidueClass

theorem windingNormalCoefficient_ne_zero : windingNormalCoefficient ≠ 0 := by
  intro hz
  apply windingResidueClass_ne_zero
  apply planeNormalIso.toLinearEquiv.injective
  change planeNormalIso.hom windingResidueClass = planeNormalIso.hom 0
  rw [map_zero]
  exact hz

/-- The logarithmic residue is a nonzero rational multiple of the actual normal generator. -/
theorem windingResidueClass_eq_smul_normal :
    windingResidueClass = windingNormalCoefficient • planeNormalClass := by
  apply planeNormalIso.toLinearEquiv.injective
  change planeNormalIso.hom windingResidueClass =
    planeNormalIso.hom (windingNormalCoefficient • planeNormalClass)
  rw [map_smul, planeNormalClass_normalization, smul_eq_mul, mul_one]
  rfl

/-- Therefore the logarithmic residue itself generates the actual normal relative group. -/
theorem windingResidueClass_generates
    (a : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology ExponentialCocycleQ.Constructions.ExponentialCocycle.Q ExponentialCocycleQ.Constructions.ExponentialCocycle.Plane ({0}ᶜ : Set ℂ) 2) :
    ∃ q : ℚ, q • windingResidueClass = a := by
  refine ⟨planeNormalIso.hom a / windingNormalCoefficient, ?_⟩
  apply planeNormalIso.toLinearEquiv.injective
  change planeNormalIso.hom ((_ : ℚ) • windingResidueClass) = planeNormalIso.hom a
  rw [map_smul]
  change (planeNormalIso.hom a / windingNormalCoefficient) * windingNormalCoefficient = _
  exact div_mul_cancel₀ _ windingNormalCoefficient_ne_zero

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.WindingResidue.Constructions.ExponentialCocycle
