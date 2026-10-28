import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainFunctoriality
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Finite Complex Local Purity -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity.Cycles

noncomputable section

/-!
# Local rational purity for finite-dimensional complex vector spaces

The actual punctured-space relative cochain complexes are transported along
continuous complex-linear equivalences. A genuine coordinate equivalence with
the standard finite complex vector space then gives local purity and a
normalized rational class. Coordinate independence is proved separately.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainFunctoriality.Cohomology

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- A continuous complex-linear equivalence as an actual topological isomorphism. -/
def complexLinearTopIso (e : E ≃L[ℂ] F) : TopCat.of E ≅ TopCat.of F :=
  TopCat.isoOfHomeo (X := TopCat.of E) (Y := TopCat.of F) e.toHomeomorph

theorem complexLinearEquiv_mapsTo_puncture (e : E ≃L[ℂ] F) :
    Set.MapsTo e ({0}ᶜ : Set E) ({0}ᶜ : Set F) := by
  intro x hx
  change x ≠ 0 at hx
  change e x ≠ 0
  exact fun he => hx (e.injective (he.trans e.map_zero.symm))

/-- Actual cochain pullback gives a contravariant isomorphism of punctured
relative cochains under a complex-linear homeomorphism. -/
def complexLinearLocalCochainIso (e : E ≃L[ℂ] F) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of F) ({0}ᶜ : Set F) ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochains (ModuleCat.of ℚ ℚ) (TopCat.of E) ({0}ᶜ : Set E) where
  hom := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
    (complexLinearTopIso e).hom (complexLinearEquiv_mapsTo_puncture e)
  inv := AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCochainsMap (ModuleCat.of ℚ ℚ)
    (complexLinearTopIso e).inv (complexLinearEquiv_mapsTo_puncture e.symm)
  hom_inv_id := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp_eq_id (ModuleCat.of ℚ ℚ)
    (complexLinearTopIso e).inv (complexLinearTopIso e).hom
    (complexLinearEquiv_mapsTo_puncture e.symm) (complexLinearEquiv_mapsTo_puncture e)
    (complexLinearTopIso e).inv_hom_id
  inv_hom_id := AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCochainsMap_comp_eq_id (ModuleCat.of ℚ ℚ)
    (complexLinearTopIso e).hom (complexLinearTopIso e).inv
    (complexLinearEquiv_mapsTo_puncture e) (complexLinearEquiv_mapsTo_puncture e.symm)
    (complexLinearTopIso e).hom_inv_id

/-- The induced isomorphism is on the genuine rational relative cohomology. -/
def complexLinearLocalCohomologyIso (e : E ≃L[ℂ] F) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of F) ({0}ᶜ : Set F) n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of E) ({0}ᶜ : Set E) n :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.up ℕ) n).mapIso
    (complexLinearLocalCochainIso e)

@[simp]
theorem complexLinearLocalCohomologyIso_hom (e : E ≃L[ℂ] F) (n : ℕ) :
    (complexLinearLocalCohomologyIso e n).hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (complexLinearTopIso e).hom (complexLinearEquiv_mapsTo_puncture e) n :=
  rfl

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- An actual continuous linear coordinate system in the full complex dimension. -/
def finiteComplexCoordinates : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
  ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm

/-- Rational local cohomology at zero, with the actual punctured complement. -/
abbrev finiteComplexLocalCohomology (n : ℕ) : ModuleCat ℚ :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of E) ({0}ᶜ : Set E) n

/-- Actual coordinates identify local cohomology with the standard normal model. -/
def finiteComplexLocalCohomologyIso (n : ℕ) :
    finiteComplexLocalCohomology E n ≅
      RationalLocalPurity.Cycles.complexNormalRationalLocalCohomology (Module.finrank ℂ E) n :=
  (complexLinearLocalCohomologyIso (finiteComplexCoordinates E) n).symm

/-- Top local rational cohomology is one-dimensional with its specified
normalization transported by an actual complex coordinate map. -/
def finiteComplexTopCohomologyIso :
    finiteComplexLocalCohomology E (2 * Module.finrank ℂ E) ≅ ModuleCat.of ℚ ℚ :=
  finiteComplexLocalCohomologyIso E (2 * Module.finrank ℂ E) ≪≫
    RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyIso (Module.finrank ℂ E)

/-- Local rational cohomology vanishes in every other degree, including the
zero-dimensional case with its genuine punctured pair. -/
theorem finiteComplexLocalCohomology_isZero (n : ℕ) (hn : n ≠ 2 * Module.finrank ℂ E) :
    IsZero (finiteComplexLocalCohomology E n) :=
  (RationalLocalPurity.Cycles.complexNormalRationalLocalCohomology_isZero (Module.finrank ℂ E) n hn).of_iso
    (finiteComplexLocalCohomologyIso E n)

/-- The normalized local rational class. -/
def finiteComplexLocalClass : finiteComplexLocalCohomology E (2 * Module.finrank ℂ E) :=
  (finiteComplexTopCohomologyIso E).inv 1

@[simp]
theorem finiteComplexLocalClass_normalization :
    (finiteComplexTopCohomologyIso E).hom (finiteComplexLocalClass E) = 1 := by
  exact (finiteComplexTopCohomologyIso E).toLinearEquiv.apply_symm_apply 1

theorem finiteComplexLocalClass_ne_zero : finiteComplexLocalClass E ≠ 0 := by
  intro h
  have heq := finiteComplexLocalClass_normalization E
  rw [h, map_zero] at heq
  exact zero_ne_one heq

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteComplexLocalPurity.Cycles
